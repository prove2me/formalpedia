-- Prove2me | solution 1 for DetDLP.m3b_ec_lookup_scan
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T22:12:17.93998+00:00
-- url     : https://prove2.me/submissions/f13f09f9-120b-495f-be48-46fab610736d

import Definitions.Def_DetDLP_M3B_ECPolyDefs
import Definitions.Def_DetDLP_W3_NativeLookupWeight
import Definitions.Def_DetDLP_W3C_BlockLookup

set_option autoImplicit false
set_option maxHeartbeats 400000
open DetDLP OAI.Algorithms.SubexponentialSAT M3B.ECPolyDefs

private theorem seed_get {α : Type} (f : α → List ℕ) (h : ∀ a, (f a).length = 4) (l : List α) (i : ℕ) (hi : i<l.length) (j : ℕ) (hj : j<4) :
    (l.flatMap f).getD (4*i+j) 0 = (f l[i]).getD j 0 := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih => cases i with
    | zero => simp [List.getD_eq_getElem?,List.getElem?_append,h,hj]
    | succ i => simpa [List.getD_eq_getElem?_getD,List.getElem?_append,h,Nat.mul_succ,show ¬(4*i+4+j<4) by omega,show 4*i+4+j-4=4*i+j by omega] using ih i (by simpa using hi)

private theorem validLookup (q : w3_Query) (i : Fin q.m) (addr : ℕ) (bs : List (List W)) (Y : List ℕ) (A : W → ℕ)
    (hB : ∀ j : Fin q.m, (bs.getD j []).length = (q.FB.blocks j).length) (bn : bs.length=q.m)
    (ha : ∀ r : Fin (q.FB.blocks i).length, A ((bs.getD i []).getD r []) = q.addr i r)
    (hy : ∀ j : Fin q.FB.totalCoords, Y.getD j 0 = (q.y j).val) :
    let b := bs.getD i []; let off := ((bs.take i.val).map List.length).sum
    ((List.range b.length).find? (fun j => decide (A (b.getD j []) = addr))).map (fun j => Y.getD (off+j) 0) =
    (w3_lookupIndex q i addr).map (fun r => (q.y (q.FB.coordOf i r)).val) := by
  let b := bs.getD i []
  let off := ((bs.take i.val).map List.length).sum
  have hr (k : ℕ) (hk : k ≤ bs.length) : ((bs.take k).map List.length).sum = ∑ j : Fin k, (bs.getD j.val []).length := by
    induction k with
    | zero => simp
    | succ k ih => rw [List.take_add_one,List.map_append,List.sum_append,ih (by omega),Fin.sum_univ_castSucc]; simp [List.getElem?_eq_getElem (by omega : k<bs.length),List.getD_eq_getElem _ _ (by omega : k<bs.length)]
  have ho : off = q.FB.blockOffset i := by
    rw [show off = _ from hr i.val (by omega)]
    unfold IndexedFactorBase.blockOffset
    apply Finset.sum_bij (fun (j : Fin i.val) _ => (⟨j.val,j.isLt.trans i.isLt⟩ : Fin q.m))
    · intro j _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,j.isLt⟩
    · intro j hj k hk he; exact Fin.ext (congrArg (Fin.val (n:=q.m)) he)
    · intro j hj; have hji : j < i := (Finset.mem_filter.mp hj).2; exact ⟨⟨j,hji⟩,Finset.mem_univ _,rfl⟩
    · intro j _; exact hB ⟨j,j.isLt.trans i.isLt⟩
  dsimp only; rw [hB i, ← show (List.finRange (q.FB.blocks i).length).map Fin.val = List.range _ by simp, List.find?_map,Option.map_map]
  change Option.map _ ((List.finRange _).find? _) = _
  simp only [Function.comp_def,ha,ho, w3_lookupIndex]
  apply congrArg (fun f => Option.map f _)
  funext r; change Y.getD (off+r.val) 0 = _; rw [ho]; exact hy (q.FB.coordOf i r)

theorem solution (q : w3_Query) (hq : w3_ecQueries q) (i : Fin q.m) (h : ℕ) :
    lookup (frames q.input) (dimensions q.input).2.2.2.1 i.val h = (w3_lookupIndex q i h).map (fun r => (q.y (q.FB.coordOf i r)).val) := by
  obtain ⟨p,ip,E,hE,_,_,_,_,_,_,_,s,F,hF,P,y,pre,rfl⟩ := hq
  letI := ecPointFintype E
  let M := Fintype.card E.toAffine.Point
  let m := blockCount (bitLen p)
  let T := hashThreshold p (M-1) m M
  let row := fun j => [(s j false).1.val+1,(s j false).2.val,(s j true).1.val+1,(s j true).2.val]
  let seeds := (List.finRange m).flatMap row
  let ws := [encodeCurveInput p E,encodeNatListBin (pointCoords P),encodeNatListBin [M,T],encodeNatListBin seeds,encodeECFactorBlocks F,encodeNatListBin (List.ofFn fun j => (y j).val),pre]
  have dec : frames (Encoding.encodeList id ws) = ws := W3C.BlockLookup.decodeFrames_correct ws
  have frameEq {α : Type} (f : α → W) (l : List α) : frames (Encoding.encodeList f l) = l.map f := W3C.BlockLookup.decodeFrames_map f l
  have bs : (frames (encodeECFactorBlocks F)).map frames = List.ofFn (fun i => (F i).map (fun P => encodeNatListBin (pointCoords P))) := by
    unfold encodeECFactorBlocks; rw [frameEq]; simp [List.map_ofFn, Function.comp_def,frameEq]
  have get (j : Fin m) : ((frames (encodeECFactorBlocks F)).map frames).getD j.val [] = (F j).map (fun P => encodeNatListBin (pointCoords P)) := by
    rw [bs,List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact j.isLt)]; simp
  let A := fun l => let pt := w5_M6Sort.decode l; let v := pt.getD 2 0%2; let ix := 4*i.val+2*v
                    if pt.getD 0 0=1 then 2*T else (seeds.getD ix 0*pt.getD 1 0+seeds.getD (ix+1) 0)%p+v*T
  let Y := List.ofFn fun j => (y j).val
  let B := (frames (encodeECFactorBlocks F)).map frames
  change lookup (frames (Encoding.encodeList id ws)) (dimensions (Encoding.encodeList id ws)).2.2.2.1 i.val h = _
  rw [dec]; have ht : (dimensions (Encoding.encodeList id ws)).2.2.2.1 = T := by simp [dimensions,dec,ws,List.getD,w5_M6Sort.decode_encode]
  rw [ht]; unfold lookup
  simp only [ws,List.getD_cons_zero,List.getD_cons_succ,w5_M6Sort.decode_encode,encodeCurveInput]
  refine validLookup _ i h B Y A ?_ ?_ ?_ ?_
  · intro j; exact (congrArg List.length (get j)).trans (List.length_map _)
  · exact (congrArg List.length bs).trans List.length_ofFn
  · intro r
    have seed (l : ℕ) (hl : l<4) : seeds.getD (4*i.val+l) 0 = (row i).getD l 0 := by
      have H := seed_get row (fun _ => rfl) (List.finRange m) i.val (by rw [List.length_finRange]; exact i.isLt) l hl
      simpa [seeds] using H
    let ew := fun P : E.toAffine.Point => encodeNatListBin (pointCoords P)
    have er : (((frames (encodeECFactorBlocks F)).map frames).getD i.val []).getD r.val [] = ew ((F i).get r) := by
      rw [get,List.getD_eq_getElem _ _ (by simpa using r.isLt)]; simp [ew]
    change A _ = _; unfold A; rw [show B.getD i.val [] = _ from get i]
    have hew : ((F i).map ew).getD r.val [] = ew ((F i).get r) := by rw [List.getD_eq_getElem _ _ (by simpa using r.isLt)]; simp
    rw [hew]; simp only [ew,w5_M6Sort.decode_encode]
    generalize he : (F i).get r = A
    cases A with
    | zero => rfl
    | some x z h =>
      change (seeds.getD (4*i.val+2*(z.val%2)) 0 * x.val + seeds.getD (4*i.val+2*(z.val%2)+1) 0)%p + z.val%2*T = _
      by_cases hz : z.val%2=1
      · rw [hz]; simp only [Nat.mul_one,one_mul,show 4*i.val+2+1=4*i.val+3 by omega,seed 2 (by decide),seed 3 (by decide)]
        simp [hz,row,List.getD] <;> rfl
      · have h0 : z.val%2=0 := by omega
        rw [h0]; simp only [Nat.mul_zero,zero_mul,add_zero,seed 1 (by decide),show seeds.getD (4*i.val) 0 = (row i).getD 0 0 from seed 0 (by decide)]
        simp [hz,row,List.getD] <;> rfl
  · intro j; change Y.getD j.val 0 = _; rw [List.getD_eq_getElem _ _ (by simp [Y])]; simp [Y]

