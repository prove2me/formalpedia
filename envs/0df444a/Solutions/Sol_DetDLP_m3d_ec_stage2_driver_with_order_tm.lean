-- Prove2me | solution 1 for DetDLP.m3d_ec_stage2_driver_with_order_tm
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T03:16:49.983804+00:00
-- url     : https://prove2.me/submissions/a1185a30-56ca-431c-8157-6ee394187f3d

import Definitions.Def_DetDLP_M3D_ECFastDefs
import Definitions.Def_DetDLP_M3D_ECPlanBridge_final
import Theorems.Thm_DetDLP_w3_ec_small_driver
import Theorems.Thm_DetDLP_m3d_ec_compiled_bounds
import Theorems.Thm_DetDLP_m3d_ec_trace_protocol
import Definitions.Def_DetDLP_W1_Bounds
import Definitions.Def_DetDLP_W5_M6TapeSimulator
import Definitions.Def_DetDLP_W3_FpWire1
import Theorems.Thm_DetDLP_stage1_complexity_dominance

set_option autoImplicit false
namespace DetDLP.M3D.Fast.BlockLookup
open DetDLP_W1_Queries OAI.Algorithms.SubexponentialSAT
private def frameStep (n : ℕ) (c : List W × W) (_ : Bool) : List W × W :=
  if c.2.headD false = true then ((first c.2 |>.take n) :: c.1, (more c.2).take n) else c
private theorem frameLen (a : W) : a.length ≤ (Encoding.frame a).length := by
  induction a with | nil => simp | cons b a ih => change a.length+1 ≤ (Encoding.frame a).length+1+1; omega
private theorem run (xs : List W) (acc : List W) (fuel : W) (n : ℕ) (hn : (Encoding.encodeList id xs).length ≤ n)
    (hf : xs.length ≤ fuel.length) : (fuel.foldl (frameStep n) (acc,Encoding.encodeList id xs)).1 = xs.reverse ++ acc := by
  induction xs generalizing acc fuel with
  | nil => induction fuel <;> simp_all [Encoding.encodeList,frameStep,List.foldl]
  | cons a xs ih => cases fuel with
    | nil => simp at hf
    | cons b fuel =>
      have ha := frameLen a
      have h := hn; simp only [Encoding.encodeList,id_eq,List.length_cons,List.length_append] at h
      simp only [List.foldl_cons,frameStep,show (Encoding.encodeList id (a::xs)).headD false = true from rfl,if_true,first_cons,more_cons,id_eq,List.take_of_length_le (show a.length ≤ n by omega),List.take_of_length_le (show (Encoding.encodeList id xs).length ≤ n by omega)]
      simpa using ih (a::acc) fuel (by omega) (by simpa using hf)
@[simp] theorem decodeFrames_correct (xs : List W) : decodeFrames (Encoding.encodeList id xs) = xs := by
  have h : xs.length ≤ (Encoding.encodeList id xs).length := by induction xs <;> simp_all [Encoding.encodeList]; omega
  change (((Encoding.encodeList id xs).foldl (frameStep _) ([],Encoding.encodeList id xs)).1).reverse = xs
  simp [run _ _ _ _ le_rfl h]


/-- The same decoder handles payloads in any canonical element encoding. -/
@[simp] theorem decodeFrames_map {β : Type*} (e : β → W) (xs : List β) :
    decodeFrames (Encoding.encodeList e xs) = xs.map e := by
  rw [← decodeFrames_correct (xs.map e)]; congr 1
  induction xs <;> simp_all [Encoding.encodeList]
@[simp] theorem decodeBlocks_correct {β : Type*} (e : β → W) (bs : List (List β)) :
    decodeBlocks (Encoding.encodeList (Encoding.encodeList e) bs) = bs.map (List.map e) := by
  simp [decodeBlocks,List.map_map,Function.comp_def]

variable {G : Type*} {m : ℕ} (FB : IndexedFactorBase G m) (enc : G → Wd)
abbrev blocks := List.ofFn fun i => (FB.blocks i).map enc
abbrev words (X : FB.BlockTuple) := (List.finRange m).flatMap fun i => [enc ((FB.blocks i).get (X i 0)), enc ((FB.blocks i).get (X i 1))]

private def inds {α : Type} (xs : List α) := List.range xs.length
private def off (bs : Blocks) (i : ℕ) := ((inds bs).map fun t => if t < i then (bs.getD t []).length else 0).sum
private def hit (bs : Blocks) (xs : List Wd) (i s k : ℕ) := if off bs i + (bs.getD i []).idxOf (xs.getD (2*i+s) []) = k then 1 else 0
private def cnt (bs : Blocks) (xs : List Wd) (k : ℕ) := ((inds bs).map fun i => hit bs xs i 0 k + hit bs xs i 1 k).sum
private def coords (bs : Blocks) := inds ([] :: [] :: bs.flatten)
private theorem pair_get {β : Type} (a b : β → W) (l : List β) (i : ℕ) (hi : i < l.length) (s : Fin 2) :
    (l.flatMap fun t => [a t,b t]).getD (2*i+s) [] = (if s=0 then a l[i] else b l[i]) := by
  induction l generalizing i with
  | nil => simp at hi
  | cons t ts ih => cases i with
    | zero => fin_cases s <;> rfl
    | succ i => simpa [Nat.mul_succ,show 2*i+2+s.val = (2*i+s.val+1)+1 by omega] using ih i (by simpa using hi)
private theorem word_get (X : FB.BlockTuple) (i : Fin m) (s : Fin 2) : (words FB enc X).getD (2*i.val+s) [] = enc ((FB.blocks i).get (X i s)) := by
  have eqi : (List.finRange m)[i.val] = i := by ext; simp
  rw [words,pair_get _ _ _ _ (by simp),eqi]; fin_cases s <;> rfl
private theorem rangeSum (n : ℕ) (f : ℕ → ℕ) : ((List.range n).map f).sum = ∑ i : Fin n, f i := by
  rw [Fin.sum_univ_eq_sum_range,← List.toFinset_range,List.sum_toFinset _ List.nodup_range]
private theorem block_get (i : Fin m) : (blocks FB enc).getD i [] = (FB.blocks i).map enc := by rw [List.getD_eq_getElem _ _ (by simp)]; simp
private theorem offset_eq (i : Fin m) : off (blocks FB enc) i = FB.blockOffset i := by
  simp only [off,inds,blocks,List.length_ofFn,rangeSum,IndexedFactorBase.blockOffset,Finset.sum_filter]; apply Finset.sum_congr rfl; intro t _; rw [block_get FB enc t,List.length_map]; rfl
variable (nd : ∀ i, ((FB.blocks i).map enc).Nodup)
include nd in
private theorem hit_eq (X : FB.BlockTuple) (i : Fin m) (s : Fin 2) (k : Fin FB.totalCoords) :
    hit (blocks FB enc) (words FB enc X) i s k = if FB.coordOf i (X i s) = k then 1 else 0 := by
  rw [hit,offset_eq,word_get,block_get]; have h := (nd i).idxOf_getElem (X i s).val (by simp)
  simp only [List.getElem_map] at h; rw [List.get_eq_getElem,h]; simp [IndexedFactorBase.coordOf,Fin.ext_iff]
include nd in
private theorem cnt_eq (X : FB.BlockTuple) (k : Fin FB.totalCoords) : cnt (blocks FB enc) (words FB enc X) k = FB.tupleCnt X k := by
  simp only [cnt,inds,blocks,List.length_ofFn,rangeSum,IndexedFactorBase.tupleCnt,Fin.sum_univ_two]; apply Finset.sum_congr rfl; intro i _; exact congrArg₂ (·+·) (hit_eq FB enc nd X i 0 k) (hit_eq FB enc nd X i 1 k)
private theorem coords_eq : coords (blocks FB enc) = List.range FB.totalCoords := by
  simp [coords,inds,blocks,List.length_flatten,List.ofFn_eq_map,List.map_map,Function.comp_def,IndexedFactorBase.totalCoords,IndexedFactorBase.totalBaseSize,Fin.sum_univ_def]
variable (M : ℕ)
include nd in
/-- The row for tuple `U j` occurs just after the leading generator constraint. -/
theorem initRowCounts_correct (U : Fin FB.totalCoords → FB.BlockTuple) (j : Fin FB.totalCoords) :
    ((initRowCounts (blocks FB enc) (words FB enc (U j)) j).map (fun z : ℤ => (z : ZMod M)), (0 : ZMod M)) =
    (List.ofFn ((w3_initRows FB M U)[j.val+1]'(by simp [w3_initRows])).1, ((w3_initRows FB M U)[j.val+1]'(by simp [w3_initRows])).2) := by
  change Prod.mk (((coords _).map fun k => (if k=j.val then 1 else 0 : ℤ) - (cnt (blocks FB enc) (words FB enc (U j)) k : ℤ)).map _) _ = _
  simp [w3_initRows,coords_eq,List.map_map]; apply List.ext_getElem <;> simp [Function.comp_def]
  intro i hi; let k : Fin FB.totalCoords := ⟨i,hi⟩; rw [cnt_eq FB enc nd (U j) k]; by_cases h : i = j.val <;> simp_all [k,w3_unitRow,Fin.ext_iff]
include nd in
/-- Coordinate reduction modulo `M` gives exactly the shift row, including its right side. -/
theorem shiftRowCounts_correct (X Y : FB.BlockTuple) :
    ((shiftRowCounts (blocks FB enc) (words FB enc X) (words FB enc Y)).map (fun z : ℤ => (z : ZMod M)), (1 : ZMod M)) =
    (List.ofFn (w3_shiftRow FB M X Y).1, (w3_shiftRow FB M X Y).2) := by
  change Prod.mk (((coords _).map fun k => (cnt (blocks FB enc) (words FB enc Y) k : ℤ) - (cnt (blocks FB enc) (words FB enc X) k : ℤ)).map _) _ = _
  simp [w3_shiftRow,coords_eq,List.map_map]; apply List.ext_getElem <;> simp [Function.comp_def]
  intro i hi; let k : Fin FB.totalCoords := ⟨i,hi⟩; rw [cnt_eq FB enc nd Y k,cnt_eq FB enc nd X k]

end DetDLP.M3D.Fast.BlockLookup
namespace DetDLP.M3D.Fast.ECRun.Assembly
open NineOracleLoop M89S1 OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
theorem liftCall (B : Fin 9 → Oracle) (j : Fin 9) {q w : Wd} {t s τ σ : ℝ}
    (run : RunsWithin (B j).1 (B j).2 q w t s) (ht : t ≤ τ) (hs : s ≤ σ) :
    Calls B τ σ (tag9 j q) w := by
  obtain ⟨n,c,hc,hh,ho,hn,hspace⟩ := run
  exact ⟨j,q,rfl,n,c,hc,hh,ho,hn.trans ht,fun k d hk hd => (hspace k d hk hd).trans hs⟩

theorem scanTrace (B : Fin 9 → Oracle) {p M K : ℕ} [Fact p.Prime]
    (E : WeierstrassCurve (ZMod p)) [E.IsElliptic] (P Q : E.toAffine.Point) (hd : ¬w3_large p M)
    {τ σ : ℝ} (order : Calls B τ σ (tag9 0 (DetDLP_M3D_orderQuery (encodeECDLPInput p E P Q))) (encodeNatListBin [M]))
    (ht : mainTimeBound K (bitLen p) ≤ τ) (hs : mainSpaceBound K (bitLen p) ≤ σ)
    (scan : w3_scanOutput M P Q (fun u => RunsWithin (B 1).1 (B 1).2 (encodeECDLPInput p E P Q)
      (countWord u) (mainTimeBound K (bitLen p)) (mainSpaceBound K (bitLen p)))) :
    w3_scanOutput M P Q (fun u => Runs (Calls B τ σ) 3 (encodeECDLPInput p E P Q) [] (countWord u)) := by
  obtain ⟨u,hu,run⟩ := scan
  refine ⟨u,hu,m3d_ec_trace_protocol.1 _ _ _ _ rfl ?_ order (liftCall B 1 run ht hs)⟩
  simpa [DetDLP_M3D_dispatch,DetDLP_M3D_scalar,encodeECDLPInput,NewtonPoly.largeCheck,S8G.FpMoment.Code.width_eq,S8G.FpMoment.Code.slots_eq,w3_large] using hd

section Native
variable {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
local notation "g" => @Fintype.card _ (ecPointFintype E)
local notation "m" => blockCount (bitLen p)
local notation "th" => hashThreshold p (g-1) m g
local notation "pt" => E.toAffine.Point

theorem winningCover (h3 : 3 < p) (large : w3_large p g) (S : ECSeed p m) (B : Fin m → List pt)
    (win : S ∈ winners ecBits (ecCost E)) (blocks : ∀ i, (B i).toFinset = ecFactorBlock E th S i) :
    ∀ X : pt, ∃ A C : Fin m → pt, (∀ i, A i ∈ B i ∧ C i ∈ B i) ∧ (∑ i, (A i+C i)) = X := by
  letI := ecPointFintype E
  have hm : 2 ≤ m := le_max_left ..
  have hg : 0 < g-1 := by have := large.2.1; omega
  have hq : 0 < qStar m g := lt_of_lt_of_le (by omega : 0 < 4096*m) (le_max_left ..)
  have hth : 0 < th := by unfold hashThreshold; apply Nat.ceil_pos.mpr; positivity
  have hw := m89_s1_winning_seed_mean.2 p m E S win
  have avg := lemma_3_2_collision_potential.1 p m h3 hm E large.2.1 large.2.2
  apply m3d_ec_plan_surjective E S B blocks ((qBlk p (g-1) th)^m)
  · unfold qBlk; positivity
  · exact (hw.trans avg).trans_lt (by norm_num)

private noncomputable def pickIndex {α : Type} {x : α} {xs : List α} (hx : x ∈ xs) : Fin xs.length :=
  (List.mem_iff_get.mp hx).choose

private theorem get_pick {α : Type} {x : α} {xs : List α} (hx : x ∈ xs) : xs[(pickIndex hx).val] = x :=
  (List.mem_iff_get.mp hx).choose_spec

noncomputable def indexed (B : Fin m → List pt) (a b : Fin m → pt) (h : ∀ i, a i ∈ B i ∧ b i ∈ B i) :
    (IndexedFactorBase.mk B).BlockTuple := fun i => ![pickIndex (h i).1,pickIndex (h i).2]

theorem indexedVal (B : Fin m → List pt) (a b : Fin m → pt) (h : ∀ i, a i ∈ B i ∧ b i ∈ B i) :
    (IndexedFactorBase.mk B).tupleVal (indexed E B a b h) = ∑ i, (a i + b i) := by
  simp [IndexedFactorBase.tupleVal,indexed,get_pick]

theorem indexedWord (B : Fin m → List pt) (a b : Fin m → pt) (h : ∀ i, a i ∈ B i ∧ b i ∈ B i) :
    BlockLookup.decodeFrames (encodeECDecomp a b) = BlockLookup.words ⟨B⟩
      (fun A => encodeNatListBin (pointCoords A)) (indexed E B a b h) := by
  simp [encodeECDecomp,BlockLookup.words,indexed,List.map_flatMap,Function.comp_def,get_pick]

end Native


end DetDLP.M3D.Fast.ECRun.Assembly

namespace DetDLP.M3D.Fast.NewtonPoly
open Groundwork DetDLP_W1_Queries OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
theorem repLabels_correct {N : ℕ} (x : Fin N → ℕ) (B : Matrix (Fin N) (Fin N) ℤ) :
    repLabels (encodeCosetRep x B) = List.ofFn x := by
  simp [repLabels,encodeCosetRep,first_cons,w5_M6Sort.decode_encode]

theorem updateWord_correct (M : ℕ) {N : ℕ} (x a : Fin N → ℕ) (B : Matrix (Fin N) (Fin N) ℤ) (rhs : ℕ) :
    updateWord M N (encodeCosetRep x B) (List.ofFn a) rhs = encodeCosetUpdateInput M x B a rhs := by
  let field (w tail : List Bool) := true :: (DetDLP_W1_Queries.frame w ++ tail)
  change field (countWord M) (field (countWord N) (field (encodeCosetRep x B) (field (encodeNatListBin (List.ofFn a)) (field (countWord rhs) [false])))) = _
  simp [field,frame_correct,encodeCosetUpdateInput,Encoding.encodeList]


end DetDLP.M3D.Fast.NewtonPoly
namespace DetDLP.M3D.Fast.ECQueryOps
open BlockLookup ECQueries Groundwork DetDLP_W1_Queries OAI.Algorithms.SubexponentialSAT
variable {p m : ℕ} [NeZero p] {E : WeierstrassCurve (ZMod p)}
local notation "encP" => (fun A : E.toAffine.Point => encodeNatListBin (pointCoords A))

private theorem flat_eq (FB : IndexedFactorBase E.toAffine.Point m) :
    (blocks FB encP).flatten = ((List.finRange m).flatMap FB.blocks).map encP := by
  simp [blocks,List.ofFn_eq_map,List.flatMap_def,List.map_flatten,List.map_map,Function.comp_def]

private theorem baseLen (FB : IndexedFactorBase E.toAffine.Point m) :
    (blocks FB encP).flatten.length = FB.totalBaseSize := by
  rw [flat_eq,List.length_map,List.length_flatMap]; exact (Fin.sum_univ_def _).symm

theorem elemWord_correct (FB : IndexedFactorBase E.toAffine.Point m) (P Q : E.toAffine.Point)
    (j : Fin FB.totalCoords) : elemWord (encodeECDLPInput p E P Q) (blocks FB encP) j = encP (FB.elem P Q j) := by
  simp only [elemWord,baseLen,IndexedFactorBase.elem]; split_ifs with h h'
  · have hh : j.val < (blocks FB encP).flatten.length := (baseLen FB).symm ▸ h
    rw [flat_eq] at hh ⊢; rw [List.getD_eq_getElem _ _ hh]
    simp
  all_goals cases P <;> cases Q <;> simp [firstPointCoords,secondPointCoords,inputFields,encodeECDLPInput,pointCoords]

theorem unitGenRow_correct (FB : IndexedFactorBase E.toAffine.Point m) :
    unitGenRow (blocks FB encP) = List.ofFn (fun j : Fin FB.totalCoords => if j = FB.genCoord then 1 else 0) := by
  apply List.ext_getElem
  · simp only [unitGenRow,List.length_map,List.length_range,List.length_cons,List.length_ofFn,baseLen]; rfl
  · intro i h k; simp only [unitGenRow,List.getElem_map,List.getElem_range,List.getElem_ofFn,baseLen,Fin.ext_iff,IndexedFactorBase.genCoord]

private def pts (FB : IndexedFactorBase E.toAffine.Point m) (X : FB.BlockTuple) :=
  (List.finRange m).flatMap fun i => [(FB.blocks i).get (X i 0),(FB.blocks i).get (X i 1)]
def bits (b : ℕ) (A : E.toAffine.Point) := (pointCoords A).flatMap (w3_bits b)

private theorem little (b x : ℕ) (h : x < 2^b) : PolyT.bval (w3_bits b x) = x := by
  unfold w3_bits
  induction b generalizing x with
  | zero =>
    obtain rfl : x=0 := by simpa using h
    rfl
  | succ b ih =>
    rw [List.ofFn_succ,PolyT.bval_cons]; simp only [Fin.val_zero,Fin.val_succ,Nat.testBit_succ]
    rw [ih (x/2) ((Nat.div_lt_iff_lt_mul (by decide)).2 (by simpa [pow_succ] using h)),Nat.testBit_zero]
    by_cases h : x%2=1 <;> simp [h] <;> omega

private theorem firstPoint_ok (b : ℕ) (hb : 1 < 2^b) (hp : p ≤ 2^b) (A : E.toAffine.Point) (rest : W) :
    readPoint b (bits b A ++ rest) = encP A := by
  have r (x : ℕ) (xs : W) : (w3_bits b x ++ xs).take b = w3_bits b x ∧ (w3_bits b x ++ xs).drop b = xs := by
    have h : (w3_bits b x).length = b := List.length_ofFn
    constructor <;> conv_lhs => arg 1; rw [← h]
    · exact List.take_append_length
    · exact List.drop_append_length
  cases A <;> simp [bits,pointCoords,readPoint,coord0,List.append_assoc,(r _ _).1,(r _ _).2,little _ _ hb,little _ 0 (by positivity),little _ _ (lt_of_lt_of_le (ZMod.val_lt _) hp)]

private theorem readMany_ok (b : ℕ) (hb : 1 < 2^b) (hp : p ≤ 2^b) (xs : List E.toAffine.Point) (rest : W) :
    readMany b xs.length (xs.flatMap (bits b) ++ rest) = xs.map encP := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have hl : (bits b a).length = 3*b := by cases a <;> simp [bits,pointCoords,w3_bits] <;> omega
    simp only [readMany,List.length_cons,List.range_succ_eq_map,List.map_cons,List.map_map,List.flatMap_cons,List.append_assoc,List.map_cons,Nat.zero_mul,List.drop_zero,firstPoint_ok _ hb hp]
    congr 1; simpa only [readMany,Function.comp_def,Nat.succ_mul,← hl,Nat.add_comm _ (bits b a).length,List.drop_length_add_append] using ih

theorem prefixToTupleWords_correct (b : ℕ) (hb : 1 < 2^b) (hp : p ≤ 2^b)
    (FB : IndexedFactorBase E.toAffine.Point m) (X Y : FB.BlockTuple) :
    prefixToTupleWords b m (w3_tupleWord FB (bits b) X Y) = (words FB encP X,words FB encP Y) := by
  have H (T : FB.BlockTuple) : (pts FB T).length = 2*m := by simp [pts,List.length_flatMap]; omega
  have H' (T : FB.BlockTuple) : ((pts FB T).flatMap (bits b)).length = 2*m*(3*b) := by
    have h (a : E.toAffine.Point) : (bits b a).length = 3*b := by cases a <;> simp [bits,pointCoords,w3_bits] <;> omega
    simp [List.length_flatMap,h,H,Nat.mul_comm]
  have hw (T : FB.BlockTuple) : (pts FB T).map encP = words FB encP T := by simp [pts,BlockLookup.words,List.map_flatMap]
  have hcode : w3_tupleWord FB (bits b) X Y = (pts FB X).flatMap (bits b) ++ (pts FB Y).flatMap (bits b) := by
    simp [w3_tupleWord,pts,List.flatMap_assoc,show List.finRange 2 = [0,1] from rfl]
  rw [prefixToTupleWords,hcode,← H' X,List.drop_append_length,← H X,readMany_ok _ hb hp,hw]
  simpa [H,hw] using congrArg (fun z => (words FB encP X,z)) (readMany_ok b hb hp (pts FB Y) [])


end DetDLP.M3D.Fast.ECQueryOps
namespace DetDLP.M3D.Fast.ECRun
open Groundwork ECStep ECQueryOps ECQueries BlockLookup DetDLP_W1_Queries OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open M89S1
variable {p m : ℕ} [NeZero p] {E : WeierstrassCurve (ZMod p)}

theorem plan_correct {p m : ℕ} (S : ECSeed p m) (T : ℕ) (c : Wd) :
    let a := Encoding.encodeList id [c,m89_ec_plan_word (some (T,S))]
    threshold a = T ∧ seedBits a = List.ofFn (ecBits S) := by
  simp [threshold,seedBits,planWord,m89_ec_plan_word]

private theorem little (b x : ℕ) (h : x < 2^b) : PolyT.bval (w3_bits b x) = x := by
  unfold w3_bits
  induction b generalizing x with
  | zero =>
    obtain rfl : x=0 := by simpa using h
    rfl
  | succ b ih =>
    rw [List.ofFn_succ,PolyT.bval_cons]; simp only [Fin.val_zero,Fin.val_succ,Nat.testBit_succ]
    rw [ih (x/2) ((Nat.div_lt_iff_lt_mul (by decide)).2 (by simpa [pow_succ] using h)),Nat.testBit_zero]
    by_cases h : x%2=1 <;> simp [h] <;> omega

private theorem packedSlice {m t b : ℕ} (f : Fin m → Fin t → ℕ) (i : Fin m) (k : Fin t) :
    (((List.ofFn (packBits (b:=b) f)).drop ((i.val*t+k.val)*b)).take b) = digitWord b (f i k) := by
  let u := finProdFinEquiv (i,k)
  have hu : u.val = i.val*t+k.val := by change k.val+t*i.val=_; ring
  have hb : (u.val+1)*b ≤ m*t*b := Nat.mul_le_mul_right _ u.isLt
  rw [Nat.add_mul,one_mul] at hb
  rw [← hu]; apply List.ext_getElem
  · simp [digitWord]; omega
  · intro j _ h; have hj : j < b := by simpa [digitWord] using h
    simp only [List.getElem_take,List.getElem_drop,List.getElem_ofFn,digitWord]
    let v : Fin b := ⟨j,hj⟩
    have hv : (finProdFinEquiv (u,v)).val = u.val*b+j := by change j+b*u.val=_; ring
    have eq : (⟨u.val*b+j,by omega⟩ : Fin (m*t*b)) = finProdFinEquiv (u,v) := Fin.ext hv.symm
    change packBits f (⟨u.val*b+j,_⟩ : Fin (m*t*b)) = (f i k).testBit v.rev.val
    rw [eq]; simp only [packBits,Equiv.symm_apply_apply,u]

omit [NeZero p] in
theorem seedChunk_correct (S : ECSeed p m) (i : Fin m) (k : Fin 4) :
    seedChunk (bitLen p) (List.ofFn (ecBits S)) (i.val*4+k.val) = ecWords S i k := by
  simp only [seedChunk,ecBits,packedSlice]
  have hlt : ecWords S i k < p := by
    unfold ecWords; dsimp only; split
    · have := (S i (decide (2 ≤ k.val))).1.isLt; omega
    · exact (S i _).2.isLt
  apply Eq.trans _ (little (bitLen p) _ (hlt.trans_le (Nat.le_pow_clog (by decide) p)))
  apply congrArg PolyT.bval; apply List.ext_getElem (by simp [digitWord,w3_bits]); intro j hj hk
  simp only [digitWord,w3_bits,List.getElem_reverse,List.getElem_ofFn,List.length_ofFn,Fin.val_rev]
  congr 1; simp only [w3_bits,List.length_ofFn] at hk; omega

omit [NeZero p] in
theorem seedNatWord_correct (S : ECSeed p m) : seedNatWord (bitLen p) m (List.ofFn (ecBits S)) =
    encodeNatListBin ((List.finRange m).flatMap fun i =>
      [(S i false).1.val+1,(S i false).2.val,(S i true).1.val+1,(S i true).2.val]) := by
  unfold seedNatWord seedNatList; congr 1
  have hr : (List.finRange m).map Fin.val = List.range m := by apply List.ext_getElem <;> simp
  rw [← hr,List.flatMap_map]; apply List.flatMap_congr; intro i _
  have h := seedChunk_correct S i
  norm_num [Function.comp_apply,Nat.mul_comm 4 i.val,ecWords] at *
  simpa [ecWords] using congrArg₂ List.cons (h 0)
    (congrArg₂ List.cons (h 1) (congrArg₂ List.cons (h 2) (congrArg (fun a => [a]) (h 3))))

theorem nativePayload_correct (M T : ℕ) (S : ECSeed p m) (P Q : E.toAffine.Point)
    (B : Fin m → List E.toAffine.Point) (x : Fin (IndexedFactorBase.mk B).totalCoords → ℕ)
    (H : Matrix _ _ ℤ) (pre : Wd) : nativePayload (bitLen p) m M (encodeECDLPInput p E P Q)
      (Encoding.encodeList id [encodeCurveInput p E,m89_ec_plan_word (some (T,S))]) (encodeECFactorBlocks B)
      (encodeCosetRep x H) pre = Encoding.encodeList id [encodeCurveInput p E,encodeNatListBin (pointCoords P),
      encodeNatListBin [M,T],encodeNatListBin ((List.finRange m).flatMap fun i =>
      [(S i false).1.val+1,(S i false).2.val,(S i true).1.val+1,(S i true).2.val]),encodeECFactorBlocks B,
      encodeNatListBin (List.ofFn x),pre] := by
  rw [nativePayload,(plan_correct S T _).1,(plan_correct S T _).2,seedNatWord_correct,NewtonPoly.repLabels_correct]
  cases P <;> simp [queryPayload,curveWord,firstPointCoords,inputFields,encodeECDLPInput,encodeCurveInput,pointCoords]

private theorem pairList_inj {α β : Type} {xs : List α} {f g : α → Fin 2 → β}
    (h : (xs.flatMap fun i => [f i 0,f i 1]) = xs.flatMap fun i => [g i 0,g i 1]) :
    ∀ i ∈ xs, ∀ j, f i j = g i j := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.flatMap_cons,List.cons_append,List.nil_append,List.cons.injEq] at h
    intro i hi j; rcases List.mem_cons.mp hi with rfl | hmem
    · fin_cases j <;> first | exact h.1 | exact h.2.1
    · exact ih h.2.2 i hmem j

private theorem encPoint_inj : Function.Injective (fun A : E.toAffine.Point => encodeNatListBin (pointCoords A)) := by
  intro A B h
  have hh := congrArg w5_M6Sort.decode h
  simp only [w5_M6Sort.decode_encode] at hh
  cases A <;> cases B <;> simp_all [pointCoords,(ZMod.val_injective p).eq_iff]

theorem tupleCode_inj (FB : IndexedFactorBase E.toAffine.Point m) (nd : ∀ i, (FB.blocks i).Nodup)
    (b : ℕ) (hb : 1<2^b) (hp : p≤2^b) : Function.Injective (Function.uncurry (w3_tupleWord FB (ECQueryOps.bits b))) := by
  let enc := fun A : E.toAffine.Point => encodeNatListBin (pointCoords A)
  have wi {X Y : FB.BlockTuple} (h : words FB enc X=words FB enc Y) : X=Y := by
    funext i j; apply (nd i).get_inj_iff.mp; apply encPoint_inj
    exact pairList_inj (f := fun i j => enc ((FB.blocks i).get (X i j)))
      (g := fun i j => enc ((FB.blocks i).get (Y i j))) h i (List.mem_finRange i) j
  rintro ⟨X,Y⟩ ⟨X',Y'⟩ he
  have h := congrArg (prefixToTupleWords b m) he
  simp only [Function.uncurry_apply_pair,prefixToTupleWords_correct b hb hp] at h
  exact Prod.ext (wi (congrArg Prod.fst h)) (wi (congrArg Prod.snd h))

theorem tupleCode_width (FB : IndexedFactorBase E.toAffine.Point m) (b : ℕ) (X Y : FB.BlockTuple) :
    (w3_tupleWord FB (ECQueryOps.bits b) X Y).length = 4*m*(3*b) := by
  have h (a : E.toAffine.Point) : (ECQueryOps.bits b a).length = 3*b := by
    cases a <;> simp [ECQueryOps.bits,pointCoords,w3_bits] <;> omega
  simp [w3_tupleWord,List.length_flatMap,h]; ring

section Native
variable {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
local notation "m₀" => blockCount (bitLen p)
local notation "M₀" => @Fintype.card _ (ecPointFintype E)
local notation "T₀" => hashThreshold p (M₀-1) m₀ M₀

omit [E.IsElliptic] in
theorem canonical_query (S : ECSeed p m₀) (B : Fin m₀ → List E.toAffine.Point) (P Q : E.toAffine.Point)
    (x : Fin (IndexedFactorBase.mk B).totalCoords → ℕ) (H : Matrix _ _ ℤ) (pre : Wd) :
    (canonical E S B P Q).query (encodeCosetRep x H) pre = Encoding.encodeList id [encodeCurveInput p E,
      encodeNatListBin (pointCoords P),encodeNatListBin [M₀,T₀],encodeNatListBin ((List.finRange m₀).flatMap fun i =>
      [(S i false).1.val+1,(S i false).2.val,(S i true).1.val+1,(S i true).2.val]),encodeECFactorBlocks B,
      encodeNatListBin (List.ofFn x),pre] := by
  apply Eq.trans _ (nativePayload_correct M₀ T₀ S P Q B x H pre)
  unfold Context.query Context.modulus Context.blocks canonical
  simp [S8G.FpMoment.Code.width_eq,primeField,inputFields,encodeECDLPInput,encodeECFactorBlocks,DetDLP_M3D_scalar,m89_ec_plan_word]

theorem nativeQ_valid (a₁ : E.a₁=0) (a₂ : E.a₂=0) (a₃ : E.a₃=0) (large : w3_large p M₀)
    (S : ECSeed p m₀) (B : Fin m₀ → List E.toAffine.Point)
    (hB : ∀ i, (B i).Nodup ∧ (B i).toFinset=ecFactorBlock E T₀ S i) (P Q : E.toAffine.Point)
    (s : w3_Rep M₀ (IndexedFactorBase.mk B).totalCoords) (f : Wd) (nz : 0<M₀) :
    w3_ecQueries (nativeQ E S B P Q nz s f) := by
  refine ⟨p,inferInstance,E,inferInstance,a₁,a₂,a₃,large.1,large.2.1,nz,large.2.2,S,B,hB,P,s.1,f,?_⟩
  unfold nativeQ; rw [Context.repWord,canonical_query]
  dsimp only; congr 1

end Native

theorem ints_correct (M : ℕ) [NeZero M] (xs : List ℤ) :
    ints M xs = xs.map (fun z : ℤ => (z : ZMod M).val) := by
  apply List.map_congr_left; intro z _
  have h : z.natAbs % M ≤ M := (Nat.mod_lt _ (NeZero.pos M)).le
  split_ifs with hz
  · rw [← ZMod.val_natCast, Nat.cast_sub h,ZMod.natCast_self,ZMod.natCast_mod]
    congr 1; rw [zero_sub,← Int.cast_natCast,← Int.cast_neg]; congr 1; omega
  · rw [← ZMod.val_natCast,← Int.cast_natCast]; congr 2; omega

section Rows
variable (FB : IndexedFactorBase E.toAffine.Point m) (M : ℕ) [NeZero M]
local notation "encP" => (fun A : E.toAffine.Point => encodeNatListBin (pointCoords A))
private theorem rowVals {N : ℕ} {xs : List ℤ} {a : Fin N → ZMod M}
    (h : xs.map (fun z : ℤ => (z : ZMod M)) = List.ofFn a) : ints M xs = List.ofFn (fun i => (a i).val) := by
  rw [ints_correct]; simpa [List.map_map,Function.comp_def] using congrArg (List.map ZMod.val) h

theorem initPacket (nd : ∀ i, ((FB.blocks i).map encP).Nodup)
    (U : Fin FB.totalCoords → FB.BlockTuple) (j : Fin FB.totalCoords)
    (t : w3_Rep M FB.totalCoords) :
    let row := (w3_initRows FB M U)[j.val+1]'(by simp [w3_initRows])
    NewtonPoly.updateWord M FB.totalCoords (Context.repWord t)
      (ints M (initRowCounts (blocks FB encP) (words FB encP (U j)) j)) 0 =
    encodeCosetUpdateInput M (fun i => (t.1 i).val) t.2 (fun i => (row.1 i).val) row.2.val := by
  dsimp only
  have h := BlockLookup.initRowCounts_correct FB encP nd M U j
  rw [rowVals M (congrArg Prod.fst h),NewtonPoly.updateWord_correct,← congrArg Prod.snd h]; simp

theorem shiftPacket (nd : ∀ i, ((FB.blocks i).map encP).Nodup)
    (b : ℕ) (hb : 1 < 2^b) (hp : p ≤ 2^b) (hM : 1 < M)
    (t : w3_Rep M FB.totalCoords) (X Y : FB.BlockTuple) :
    let xy := prefixToTupleWords b m (w3_tupleWord FB (ECQueryOps.bits b) X Y)
    let row := w3_shiftRow FB M X Y
    NewtonPoly.updateWord M FB.totalCoords (Context.repWord t)
      (ints M (shiftRowCounts (blocks FB encP) xy.1 xy.2)) 1 =
    encodeCosetUpdateInput M (fun i => (t.1 i).val) t.2 (fun i => (row.1 i).val) row.2.val := by
  rw [prefixToTupleWords_correct b hb hp FB X Y]; dsimp only
  have h := BlockLookup.shiftRowCounts_correct FB encP nd M X Y
  rw [rowVals M (congrArg Prod.fst h),NewtonPoly.updateWord_correct,← congrArg Prod.snd h]
  simp [ZMod.val_one_eq_one_mod,Nat.mod_eq_of_lt hM]
end Rows

private theorem encMap {α : Type} (e : α → Wd) (xs : List α) :
    fr (xs.map e) = Encoding.encodeList e xs := by
  induction xs <;> simp_all [fr,Encoding.encodeList]

theorem idRep_correct (bs : Blocks) {N : ℕ} (hN : bs.flatten.length+2=N) (M : ℕ) [NeZero M] :
    idRep bs = Context.repWord (w3_full M N) := by
  have h : ECStep.inds bs = (List.finRange N).map Fin.val := by
    apply List.ext_getElem <;> simp [ECStep.inds,← hN]
  unfold idRep Context.repWord w3_full encodeCosetRep; rw [h,← encMap encodeIntBin]
  simp only [List.map_map,List.flatMap_map,List.map_flatMap,List.ofFn_eq_map,Function.comp_def,
    Pi.zero_apply,ZMod.val_zero,Matrix.one_apply,Fin.ext_iff]
  simp only [apply_ite encodeIntBin]; rfl


theorem genPacket (FB : IndexedFactorBase E.toAffine.Point m) (M : ℕ) [NeZero M] (hM : 1 < M) :
    let bs := blocks FB (fun A => encodeNatListBin (pointCoords A))
    NewtonPoly.updateWord M FB.totalCoords (idRep bs) (unitGenRow bs) 1 =
    encodeCosetUpdateInput M (fun _ : Fin FB.totalCoords => 0) (1 : Matrix _ _ ℤ)
      (fun i => (w3_unitRow FB M FB.genCoord i).val) (1 : ZMod M).val := by
  dsimp only
  have hN : (blocks FB (fun A => encodeNatListBin (pointCoords A))).flatten.length+2=FB.totalCoords := by
    simp [blocks,List.length_flatten,List.ofFn_eq_map,List.map_map,Function.comp_def,
      IndexedFactorBase.totalCoords,IndexedFactorBase.totalBaseSize,Fin.sum_univ_def]
  rw [idRep_correct _ hN M,unitGenRow_correct,NewtonPoly.updateWord_correct]
  simp [w3_unitRow,w3_full,apply_ite ZMod.val,ZMod.val_one_eq_one_mod,Nat.mod_eq_of_lt hM]

end DetDLP.M3D.Fast.ECRun

namespace DetDLP.M3D.Fast.ECRun.Assembly
section Labels
variable {G : Type*} {m : ℕ} (FB : IndexedFactorBase G m) (M : ℕ) [NeZero M]

private theorem w3_sum_slots (X : FB.BlockTuple) (v : Fin FB.totalCoords → ℤ) :
    (∑ j, (FB.tupleCnt X j : ℤ) * v j) = ∑ i, ∑ k, v (FB.coordOf i (X i k)) := by
  classical
  simp only [IndexedFactorBase.tupleCnt, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.sum_mul]
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro k _
  simp [ite_mul]

private theorem w3_label_cast (y : w3_Label M FB.totalCoords) (X : FB.BlockTuple) :
    ((FB.tupleLabelSum M y X : ℤ) : ZMod M) = ∑ i, (FB.tupleCnt X i : ZMod M) * y i := by
  simp [IndexedFactorBase.tupleLabelSum, ZMod.natCast_zmod_val]

private theorem w3_row_eq (y : w3_Label M FB.totalCoords) (X Y : FB.BlockTuple) :
    w3_holds (w3_shiftRow FB M X Y) y ↔ ((w3_delta FB M y X Y : ℤ) : ZMod M) = 1 := by
  simp only [w3_holds,w3_shiftRow,sub_mul,Finset.sum_sub_distrib,w3_delta,Int.cast_sub,w3_label_cast]

private theorem w3_init_iff (U : Fin FB.totalCoords → FB.BlockTuple) (y : w3_Label M FB.totalCoords) :
    (∀ r ∈ w3_initRows FB M U, w3_holds r y) ↔ FB.SatisfiesInitialCongruences M U y := by
  classical
  simp [w3_initRows,w3_holds,w3_unitRow,IndexedFactorBase.SatisfiesInitialCongruences,
    w3_label_cast,sub_mul,Finset.sum_sub_distrib,ite_mul,sub_eq_zero]

private theorem w3_flat_slot {n : ℕ} (F : Fin n → List G) (i : Fin n) (r : Fin (F i).length) :
    ((List.finRange n).flatMap F)[(∑ j ∈ Finset.univ.filter (fun j : Fin n => j < i), (F j).length) + r.val]? = some ((F i).get r) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i r
    · intro s; simp [List.finRange_succ,List.flatMap_cons,List.getElem?_append,s.isLt]
    · intro s
      have hsum : (∑ t ∈ Finset.univ.filter (fun t : Fin (n+1) => t < j.succ), (F t).length) =
          (F 0).length + ∑ t ∈ Finset.univ.filter (fun t : Fin n => t < j), (F t.succ).length := by
        simp only [Finset.sum_filter,Fin.sum_univ_succ,Fin.succ_pos,if_true,Fin.succ_lt_succ_iff]
      simpa [List.finRange_succ,List.flatMap_cons,List.flatMap_map,hsum,Nat.add_assoc,
        List.getElem?_append,Function.comp_def] using ih (fun t => F t.succ) j s

private theorem w3_elem_slot (P Q : G) (i : Fin m) (r : Fin (FB.blocks i).length) :
    FB.elem P Q (FB.coordOf i r) = (FB.blocks i).get r := by
  have h := FB.blockOffset_add_lt i r
  have hlen : FB.blockOffset i + r.val < ((List.finRange m).flatMap FB.blocks).length := by
    rw [List.length_flatMap, ← Fin.sum_univ_def]; exact h
  have he := w3_flat_slot FB.blocks i r
  change ((List.finRange m).flatMap FB.blocks)[FB.blockOffset i + r.val]? = some _ at he
  rw [List.getElem?_eq_getElem hlen] at he
  unfold IndexedFactorBase.elem
  rw [dif_pos (show (FB.coordOf i r).val < FB.totalBaseSize from h)]
  exact Option.some.inj he

end Labels

/-- The true labels satisfy every initializing row and every shift. -/
theorem recoverLabels {V : Type} [AddCommGroup V] [Fintype V] [DecidableEq V] {M m : ℕ} [NeZero M]
    (hcard : Nat.card V = M) (P Q : V) (hg : addOrderOf P = M)
    (FB : IndexedFactorBase V m) (U : Fin FB.totalCoords → FB.BlockTuple)
    (hU : ∀ j, FB.tupleVal (U j) = FB.elem P Q j) : ∃ z : w3_Label M FB.totalCoords,
    (∀ r ∈ w3_initRows FB M U, w3_holds r z) ∧ w3_pass FB M P z := by
  classical
  have ht : AddSubgroup.zmultiples P = ⊤ := (AddSubgroup.zmultiples P).eq_top_of_card_eq
    ((Nat.card_zmultiples P).trans (hg.trans hcard.symm))
  have all (g : V) : g ∈ AddSubgroup.zmultiples P := by rw [ht]; trivial
  let e := (zmodAddEquivOfGenerator all hcard).symm
  have hP : e P = 1 := zmodAddEquivOfGenerator_symm_apply_generator all hcard
  let lam : w3_Label M FB.totalCoords := fun j => e (FB.elem P Q j)
  have hlam (j) : (lam j).val • P = FB.elem P Q j := by
    apply e.injective; simp [hP,nsmul_eq_mul, ZMod.natCast_zmod_val,lam]
  have htarget : FB.elem P Q FB.targetCoord = Q := by simp [IndexedFactorBase.elem,IndexedFactorBase.targetCoord]
  have hgen : FB.elem P Q FB.genCoord = P := by simp [IndexedFactorBase.elem,IndexedFactorBase.genCoord]
  have hsum (T : FB.BlockTuple) : ((FB.tupleLabelSum M lam T : ℤ) : ZMod M) = e (FB.tupleVal T) := by
    unfold IndexedFactorBase.tupleLabelSum; rw [w3_sum_slots]; push_cast
    simp [IndexedFactorBase.tupleVal,Fin.sum_univ_two,lam,w3_elem_slot,ZMod.natCast_zmod_val]
  have hli : FB.SatisfiesInitialCongruences M U lam := ⟨by simp [lam,hgen,hP],fun j => by rw [hsum,hU]⟩
  have hlp : w3_pass FB M P lam := by
    intro X Y h; rw [w3_row_eq]; simp [w3_delta,hsum,h,map_add,hP]
  exact ⟨lam,(w3_init_iff FB M U lam).2 hli,hlp⟩

open NineOracleLoop Stage2Trace Context OAI.Algorithms.SubexponentialSAT.Computation

/-- Lift one canonical HNF call, retaining the true solution and the conditional halving guarantee. -/
theorem updateCall (bank : Fin 9 → Oracle) {K M N : ℕ} [NeZero M] {τ σ : ℝ}
    (s : w3_Rep M N) (r : w3_Row M N) (z : w3_Label M N)
    (inv : Invariant z s) (good : w3_holds r z)
    (op : IsModularLatticeBasis M s.2 → (∃ x ∈ w3_coset s, w3_holds r x) →
      ∃ t, w3_update r s t ∧ (¬w3_holds r s.1 → 2*Nat.card (w3_coset t) ≤ Nat.card (w3_coset s)) ∧
        RunsWithin (bank 8).1 (bank 8).2 (encodeCosetUpdateInput M (fun i => (s.1 i).val) s.2
          (fun i => (r.1 i).val) r.2.val) (repWord t) (polyBound K (N+bitLen M)) (polyBound K (N+bitLen M)))
    (ht : polyBound K (N+bitLen M) ≤ τ) (hs : polyBound K (N+bitLen M) ≤ σ) :
    ∃ t, w3_update r s t ∧ Invariant z t ∧ (¬w3_holds r s.1 → 2*Nat.card (w3_coset t) ≤ Nat.card (w3_coset s)) ∧
      Calls bank τ σ (tag9 8 (encodeCosetUpdateInput M (fun i => (s.1 i).val) s.2 (fun i => (r.1 i).val) r.2.val)) (repWord t) := by
  obtain ⟨t,hu,half,run⟩ := op inv.1 ⟨z,inv.2,good⟩
  exact ⟨t,hu,⟨hu.1,hu.2.symm ▸ ⟨inv.2,good⟩⟩,half,liftCall bank 8 run ht hs⟩

/-- A bank is compiled once, before any input or choice of branch. -/
theorem compileBank (bank : Fin 9 → Oracle) (J : ℕ) :
    ∃ (D : PrimitiveMachine) (out : Fin D.tapeCount) (H : ℕ), ∀ {b : ℕ} {i y : Wd} {r : ℕ} {τ σ : ℝ},
      1 ≤ b → i.headD true = true → 1 ≤ r → 0 ≤ τ → 0 ≤ σ →
      (i.length : ℝ)+r+2*σ+8 ≤ mainSpaceBound J b → τ ≤ mainTimeBound J b →
      Runs (Calls bank τ σ) r i [] y → RunsWithin D out i y (mainTimeBound H b) (mainSpaceBound H b) :=
  m3d_ec_compiled_bounds (fun j => (bank j).1) (fun j => (bank j).2) J

end DetDLP.M3D.Fast.ECRun.Assembly

namespace DetDLP.M3D.Fast.ECRun.Assembly
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open DetDLP_W1_Bounds
noncomputable section
set_option maxHeartbeats 1200000
private def base (k b : ℕ) := ⌊mainSpaceBound k b⌋₊ + b + k + 100
private def lim (k b : ℕ) := 1000*(base k b+1)^5
private def pol (k n : ℕ) := k*(n+1)^k
private def netLim (k b : ℕ) := k*(lim k b)^2 + pol k (lim k b) + 9
private def space (k b : ℕ) := mainSpaceBound k b + pol k (netLim k b + lim k b) + 1
private def timeB (k b : ℕ) := (space k b+1)*(mainTimeBound k b+1)
private theorem pol_eq (k n : ℕ) : (pol k n : ℝ) = polyBound k n := by simp [pol,polyBound]
private theorem space_pos (k b : ℕ) : 0 ≤ space k b := by unfold space mainSpaceBound; positivity
private theorem time_pos (k b : ℕ) : 0 ≤ timeB k b := by unfold timeB; have := space_pos k b; unfold mainTimeBound; positivity
private theorem budget (k : ℕ) : ∃ J, ∀ p ≥ 2, let b := bitLen p
    2*(lim k b : ℝ)+2*space k b+8 ≤ mainSpaceBound J b ∧ timeB k b ≤ mainTimeBound J b := by
  let I := {p : ℕ // 2 ≤ p}
  let b (i : I) := bitLen i.val
  let S (i : I) := sScale (b i)
  let T (i : I) := 4*tScale (b i)
  have hS (i) : 1 ≤ S i := scales_one (Nat.clog_pos (by decide) i.property)
  have hST (i) : S i ≤ T i := compareScale _
  have hT (i) := (hS i).trans (hST i)
  have ds : Dom S (fun i => mainSpaceBound k (b i)) := ⟨k, fun _ => (sEq ..).ge⟩
  have ds0 (i) : 0 ≤ mainSpaceBound k (b i) := by unfold mainSpaceBound; positivity
  have dF := ds.weaken (fun i => Nat.floor_le (ds0 i))
  obtain ⟨c,hc⟩ := stage1_complexity_dominance.2.2.1 1 0
  have db : Dom S (fun i => (b i : ℝ)) := by
    refine ⟨c,fun i => ?_⟩; change (bitLen i.val : ℝ) ≤ DetDLP_W1_Bounds.E (sScale _) _; rw [sEq]
    have h := (hc i.val 0 i.property (by omega)).1; simp [polyBound] at h; linarith
  have cst := dconst hS
  have dbase : Dom S (fun i => (base k (b i) : ℝ)) := by simpa [base] using (((dF.add hS db).add hS (cst k)).add hS (cst 100))
  have dl : Dom S (fun i => (lim k (b i) : ℝ)) := by simpa [lim] using (cst 1000).mul ((dbase.add hS (cst 1)).pow hS (fun _ => by positivity) 5) (fun _ => by positivity) (fun _ => by positivity)
  have dp (f : I → ℕ) (hf : Dom S (fun i => (f i : ℝ))) : Dom S (fun i => (pol k (f i) : ℝ)) := by
    simpa [pol] using (cst k).mul ((hf.add hS (cst 1)).pow hS (fun _ => by positivity) k) (fun _ => by positivity) (fun _ => by positivity)
  have dn : Dom S (fun i => (netLim k (b i) : ℝ)) := by
    simpa [netLim] using (((cst k).mul (dl.pow hS (fun _ => by positivity) 2) (fun _ => by positivity) (fun _ => by positivity)).add hS (dp _ dl)).add hS (cst 9)
  have dsp : Dom S (fun i => space k (b i)) := by simpa [space] using (ds.add hS (dp (fun i => netLim k (b i)+lim k (b i)) (by simpa using dn.add hS dl))).add hS (cst 1)
  have dspace := (((cst 2).mul dl (fun _ => by norm_num) (fun _ => by positivity)).add hS ((cst 2).mul dsp (fun _ => by norm_num) (fun _ => space_pos ..))).add hS (cst 8)
  have dt : Dom T (fun i => mainTimeBound k (b i)) := by
    refine ⟨k,fun i => ?_⟩; dsimp only; rw [←tEq]; apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have h : 0 ≤ tScale (b i) := by unfold tScale; positivity
    exact mul_le_mul_of_nonneg_left (by dsimp [T]; linarith) (Nat.cast_nonneg _)
  have dtime := (liftTime hS hST (dsp.add hS (cst 1))).mul (dt.add hT (dconst hT 1)) (fun i => by have := space_pos k (b i); positivity) (fun i => by unfold mainTimeBound; positivity)
  obtain ⟨j,hj⟩ := dspace; obtain ⟨l,hl⟩ := dtime
  refine ⟨max j (4*l),fun p hp => ?_⟩; let i : I := ⟨p,hp⟩
  constructor
  · rw [←sEq]; exact (hj i).trans (monoE (by linarith [hS i]) (le_max_left ..))
  · rw [←tEq]; have eq : DetDLP_W1_Bounds.E (T i) l = DetDLP_W1_Bounds.E (tScale (b i)) (4*l) := by unfold DetDLP_W1_Bounds.E T; push_cast; congr 1; ring
    simpa only [timeB,Nat.cast_one] using (hl i).trans (le_trans (le_of_eq eq) (monoE (by unfold tScale; positivity) (le_max_right j (4*l))))

open M89S1 NineOracleLoop Stage2Trace Context ECQueries ECQueryOps BlockLookup
private theorem outLen {D : PrimitiveMachine} {o : Fin D.tapeCount} {i w : Wd} {t s : ℝ}
    (h : RunsWithin D o i w t s) : w.length ≤ ⌊s⌋₊+8 := by
  obtain ⟨k,c,_,_,eq,tr⟩ := w5_EntryTapeCode.call D o i w t s h (fun _ => false) (fun _ => none)
  have hb := tr.prefix le_rfl tr.trace (w5_EntryTapeCode.lane D o false true)
  rw [← eq]; refine le_trans ?_ hb
  generalize c.stacks (w5_EntryTapeCode.lane D o false true) = tags
  generalize c.stacks (w5_EntryTapeCode.lane D o false false) = vals
  induction tags generalizing vals with
  | nil => rfl
  | cons a l ih => cases a <;> cases vals <;> simp [w5_EntryTapeCode.extract,ih]
private theorem listLen {α : Type} (f : α → Wd) (xs : List α) (H : ℕ) (h : ∀ x ∈ xs, (f x).length ≤ H) :
    (Encoding.encodeList f xs).length ≤ xs.length*(2*H+2)+1 := by
  induction xs with
  | nil => simp [Encoding.encodeList]
  | cons a xs ih =>
    have := h a List.mem_cons_self; specialize ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [Encoding.encodeList,List.length_cons,List.length_append,w3_frameLength,Nat.succ_mul] at *; omega
private theorem binaryLen {x p : ℕ} (h : x ≤ p) : (countWord x).length ≤ bitLen p+1 := by
  by_cases hx : x=0
  · simp [countWord,hx]
  rw [countWord,if_neg hx,Nat.size_eq_bits_len]; apply Nat.size_le.mpr
  exact h.trans_lt ((Nat.le_pow_clog (by decide : 1<2) p).trans_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)))
private theorem coords_le {p : ℕ} [Fact p.Prime] {E : WeierstrassCurve (ZMod p)} (P : E.toAffine.Point) :
    (pointCoords P).length=3 ∧ ∀ x ∈ pointCoords P, x ≤ p := by
  cases P <;> simp [pointCoords,(ZMod.val_lt _).le, (Fact.out : p.Prime).one_lt.le]
private theorem curve_le {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) : (encodeCurveInput p E).length ≤ 6*(2*(bitLen p+1)+2)+1 := by
  apply listLen countWord _ (bitLen p+1); intro x h; apply binaryLen
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h; rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> first | exact le_rfl | exact (ZMod.val_lt _).le
private theorem input_le {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) (P Q : E.toAffine.Point) :
    (encodeECDLPInput p E P Q).length ≤ 12*(2*(bitLen p+1)+2)+1 := by
  unfold encodeECDLPInput encodeNatListBin
  apply le_trans (listLen _ _ (bitLen p+1) ?_)
  · simp [(coords_le P).1,(coords_le Q).1]
  · intro x hx; apply binaryLen; simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with (((rfl|rfl|rfl|rfl|rfl|rfl)|h)|h) <;> first | exact le_rfl | exact (ZMod.val_lt _).le | exact (coords_le P).2 _ h | exact (coords_le Q).2 _ h
private theorem total_le {p m : ℕ} [NeZero p] {E : WeierstrassCurve (ZMod p)} (B : Fin m → List E.toAffine.Point) :
    (IndexedFactorBase.mk B).totalBaseSize ≤ (encodeECFactorBlocks B).length := by
  let enc := fun A : E.toAffine.Point => encodeNatListBin (pointCoords A)
  have gen (xs : List (List E.toAffine.Point)) : (xs.map List.length).sum ≤ (Encoding.encodeList (Encoding.encodeList enc) xs).length := by
    induction xs with
    | nil => simp
    | cons x xs ih => have := w3_encodedCount enc x; simp [Encoding.encodeList,w3_frameLength] at *; omega
  simpa [encodeECFactorBlocks,IndexedFactorBase.totalBaseSize,List.ofFn_eq_map,List.map_map,Function.comp_def,Fin.sum_univ_def,enc] using gen (List.ofFn B)
private theorem blockUpper (b : ℕ) : blockCount b ≤ b+2 := by
  apply max_le (by omega) (Nat.ceil_le.mpr ?_)
  have u : Nat.clog 2 (b+2) ≤ b+2 := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2 (Nat.lt_pow_self (by decide)).le
  have v : 1 ≤ Nat.clog 2 (b+2) := Nat.clog_pos (by decide) (by omega)
  exact (Real.rpow_le_self_of_one_le (by exact_mod_cast v) (by norm_num)).trans (by exact_mod_cast u)
private theorem polyMono {a k n l : ℕ} (ha : a ≤ k) (hn : n ≤ l) : polyBound a n ≤ polyBound k l := by
  apply ((stage1_complexity_dominance.1 a k n ha).2).trans; unfold polyBound; gcongr
private theorem timeMono {a k b : ℕ} (ha : a ≤ k) : mainTimeBound a b ≤ mainTimeBound k b := by
  rw [←tEq,←tEq]; exact monoE (by unfold tScale; positivity) ha
private theorem fullInv {M N : ℕ} [NeZero M] (z : w3_Label M N) : Invariant z (w3_full M N) := by
  constructor
  · refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · intro i j hij; simp [w3_full, Matrix.one_apply, ne_of_lt hij]
    · intro i; simp [w3_full]
    · intro i j hji; simp [w3_full, Matrix.one_apply, ne_of_gt hji]
    · intro v; exact ⟨_, (Matrix.one_mulVec _).symm⟩
    · simp [w3_full]
  · refine ⟨fun i => ((z i).val : ℤ), ?_⟩; intro i; simp [w3_full,ZMod.natCast_zmod_val]

section Numeric
variable {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
local notation "b₀" => bitLen p
local notation "m₀" => blockCount b₀
local notation "M₀" => @Fintype.card _ (ecPointFintype E)
local notation "T₀" => hashThreshold p (M₀-1) m₀ M₀
private theorem queryLen (S : ECSeed p m₀) (B : Fin m₀ → List E.toAffine.Point) (P Q : E.toAffine.Point)
    (x : Fin (IndexedFactorBase.mk B).totalCoords → ℕ) (H : Matrix _ _ ℤ) (pre : Wd) (k : ℕ)
    (hm : m₀ ≤ base k b₀) (hN : (IndexedFactorBase.mk B).totalCoords ≤ base k b₀)
    (hB : (encodeECFactorBlocks B).length ≤ base k b₀) (hM : (countWord M₀).length ≤ base k b₀)
    (hT : (countWord T₀).length ≤ base k b₀) (hx : ∀ i, x i < M₀) (hf : pre.length ≤ 4*m₀*(3*b₀)) :
    ((canonical E S B P Q).query (encodeCosetRep x H) pre).length ≤ lim k b₀ := by
  let d := base k b₀
  have hb : b₀+1 ≤ d := by simp only [d,base]; omega
  have hM' : bitLen M₀ ≤ d := (w3_clogWord _).trans hM
  have hpnt := listLen countWord (pointCoords P) (b₀+1) (fun x h => binaryLen ((coords_le P).2 x h))
  rw [(coords_le P).1] at hpnt
  let seed := (List.finRange m₀).flatMap fun i => [(S i false).1.val+1,(S i false).2.val,(S i true).1.val+1,(S i true).2.val]
  have hs : (encodeNatListBin seed).length ≤ 4*m₀*(2*(b₀+1)+2)+1 := by
    apply le_trans (listLen _ _ (b₀+1) ?_)
    · simp [seed,List.length_flatMap,Nat.mul_comm]
    · intro a ha; apply binaryLen; obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; rcases hi with rfl|rfl|rfl|rfl <;> have h := (S i false).1.isLt <;> have h' := (S i true).1.isLt <;> have h'' := (S i false).2.isLt <;> have h''' := (S i true).2.isLt <;> omega
  have hxs := listLen countWord (List.ofFn x) (d+1) (by intro a ha; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha; exact (binaryLen (hx i).le).trans (by omega))
  rw [List.length_ofFn] at hxs
  rw [canonical_query]
  change (Encoding.encodeList id [encodeCurveInput p E,encodeNatListBin (pointCoords P),encodeNatListBin [M₀,T₀],encodeNatListBin seed,encodeECFactorBlocks B,encodeNatListBin (List.ofFn x),pre]).length ≤ _
  have hmt : (encodeNatListBin [M₀,T₀]).length ≤ 2*(2*d+2)+1 := listLen _ _ _ (by simpa [d] using And.intro hM hT)
  have hcur := curve_le E
  change (encodeNatListBin (pointCoords P)).length ≤ _ at hpnt
  change (encodeNatListBin (List.ofFn x)).length ≤ _ at hxs
  change _ ≤ d at hm hN hB
  have hs' := hs.trans (show 4*m₀*(2*(b₀+1)+2)+1 ≤ 4*d*(2*d+2)+1 by gcongr)
  have hf' := hf.trans (show 4*m₀*(3*b₀) ≤ 4*d*(3*d) by gcongr <;> omega)
  have hx' := hxs.trans (show _ ≤ d*(2*(d+1)+2)+1 by gcongr)
  simp only [Encoding.encodeList,id_eq,List.length_cons,List.length_append,List.length_nil,w3_frameLength]
  change _ ≤ 1000*(d+1)^5; nlinarith only [hs',hf',hx',hmt,hcur,hpnt,hB,hb,Nat.zero_le (d^5),Nat.zero_le (d^4),Nat.zero_le (d^3),Nat.zero_le (d^2),Nat.zero_le d]
end Numeric

private theorem smallNum (k b : ℕ) : let d := base k b; let L := lim k b
    12*(2*(b+1)+2)+1 ≤ L ∧ 3 ≤ L ∧ b ≤ L ∧ d+d ≤ L ∧ blockCount b ≤ d := by
  dsimp only; let d := base k b; have hb : b+2 ≤ d := by dsimp [d,base]; omega
  have g : d+1 ≤ (d+1)^5 := Nat.le_self_pow (by decide) _
  have hm := blockUpper b
  change _ ≤ 1000*(d+1)^5 ∧ _ ≤ 1000*(d+1)^5 ∧ _ ≤ 1000*(d+1)^5 ∧ _ ≤ 1000*(d+1)^5 ∧ _ ≤ d
  omega
private theorem fuelBound {k b M N n m : ℕ} (hm : m ≤ base k b) (hN : N ≤ base k b) (hM : bitLen M ≤ base k b)
    (hn : n ≤ Nat.clog 2 (M^N)) : 2+n*(2*(4*m*(3*b))+3)+2*N+5 ≤ lim k b := by
  let d := base k b; have hb : b ≤ d := by unfold d base; omega
  have hcl : Nat.clog 2 (M^N) ≤ bitLen M*N := Nat.clog_le_of_le_pow (by rw [Nat.pow_mul]; exact Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) M) _)
  have hnn : n ≤ d*d := (hn.trans hcl).trans (Nat.mul_le_mul hM hN)
  calc _ ≤ 2+(d*d)*(2*(4*d*(3*d))+3)+2*d+5 := by gcongr
       _ ≤ 1000*(d+1)^5 := by nlinarith only [Nat.zero_le (d^5),Nat.zero_le (d^4),Nat.zero_le (d^3),Nat.zero_le (d^2),Nat.zero_le d]

theorem driver
    (hord : DetDLP.M89S1.CountOracle)
    (en : PrimitiveMachine) (eo : Fin en.tapeCount) (de : PrimitiveMachine) (do' : Fin de.tapeCount) (K : ℕ)
    (hnet : w3_terminalOps w3_ecQueries) (hupdate : w3_hnfOps) :
    ∃ (D : PrimitiveMachine) (out : Fin D.tapeCount) (C : ℕ),
      ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
        E.a₁ = 0 → E.a₂ = 0 → E.a₃ = 0 →
        letI := ecPointFintype E
        let M := Fintype.card E.toAffine.Point
        let m := blockCount (bitLen p)
        M.Prime → ∀ (P Q : E.toAffine.Point), addOrderOf P = M →
          let accepts := fun u => RunsWithin D out (encodeECDLPInput p E P Q) (countWord u)
                                    (mainTimeBound C (bitLen p)) (mainSpaceBound C (bitLen p))
          (¬ w3_large p M → w3_scanOutput M P Q accepts) ∧
          (w3_large p M → ∀ F : Fin m → List E.toAffine.Point, w3_ecBaseCalls en eo de do' K E F →
            ∃ (seed : ECSeed p m) (B : Fin m → List E.toAffine.Point),
              (∀ i, (B i).Nodup ∧ (B i).toFinset = ecFactorBlock E (hashThreshold p (M-1) m M) seed i) ∧
              w3_traceOutput ⟨F⟩ ⟨B⟩ M P Q accepts) := by
  classical
  obtain ⟨S₁,o₁,k₁,scan⟩ := w3_ec_small_driver
  obtain ⟨S₂,o₂,S₃,o₃,k₂,k₃,plan⟩ := m3d_ec_plan_base hord
  obtain ⟨S₅,o₅,k₅,decode⟩ := m3d_ec_plan_decode hord
  obtain ⟨S₀,o₀,k₀,order⟩ := hord
  obtain ⟨c,g,S₆,o₆,_,_,S₇,o₇,k₇,_,_,network⟩ := hnet
  obtain ⟨S₈,o₈,k₈,update⟩ := hupdate
  let A := bank ⟨S₀,o₀⟩ ⟨S₁,o₁⟩ ⟨S₂,o₂⟩ ⟨S₃,o₃⟩ ⟨S₅,o₅⟩ ⟨S₆,o₆⟩ ⟨S₇,o₇⟩ ⟨S₈,o₈⟩
  let v := k₀+k₁+k₂+k₃+k₅+c+g+k₇+k₈
  obtain ⟨w,hw⟩ := stage1_complexity_dominance.2.2.1 v 0
  let k := v+w
  obtain ⟨J,hJ⟩ := budget k
  obtain ⟨D,out,C,compile⟩ := compileBank A J
  refine ⟨D,out,C,?_⟩; intro p hp h3 E hE a₁ a₂ a₃
  letI := ecPointFintype E
  let M := Fintype.card E.toAffine.Point
  let b := bitLen p; let m := blockCount b
  dsimp only
  intro prime P Q hg
  let i := encodeECDLPInput p E P Q
  let d := base k b; let L := lim k b; let σ := space k b; let τ := timeB k b
  have hle : v ≤ k := Nat.le_add_right ..
  have pos : 0 ≤ mainSpaceBound k b := by unfold mainSpaceBound; positivity
  have pt : 0 ≤ mainTimeBound k b := by unfold mainTimeBound; positivity
  have hb : 1 ≤ b := Nat.clog_pos (by decide) (by omega : 1<p)
  have hσ : 0 ≤ σ := space_pos ..; have hτ : 0 ≤ τ := time_pos ..
  have hst : σ ≤ τ := by dsimp [τ,timeB]; nlinarith [mul_nonneg hσ pt]
  have hspace {j : ℕ} (h : j ≤ v) : mainSpaceBound j b ≤ mainSpaceBound k b := (stage1_complexity_dominance.1 _ _ _ (h.trans hle)).1
  have hpoly {j : ℕ} (h : j ≤ v) : polyBound j b ≤ mainSpaceBound k b := ((stage1_complexity_dominance.1 _ _ _ h).2.trans (hw p 0 (by omega) (by omega)).1).trans ((stage1_complexity_dominance.1 w k b (by dsimp [k]; omega)).1)
  have ss : mainSpaceBound k b ≤ σ := by dsimp [σ,space]; linarith [Nat.cast_nonneg (α:=ℝ) (pol k (netLim k b+lim k b))]
  have tt : mainTimeBound k b ≤ τ := by dsimp [τ,timeB]; nlinarith [mul_nonneg hσ pt]
  have wide {j n : ℕ} (hj : j ≤ v) (hn : n ≤ netLim k b + L) : polyBound j n ≤ σ := by
    apply (polyMono (hj.trans hle) hn).trans; rw [←pol_eq]; dsimp [σ,space,L]; linarith
  have lens := smallNum k b
  have hi : i.length ≤ L := (input_le E P Q).trans lens.1
  have headi : i.headD true=true := rfl
  have machine {r u : ℕ} (hr : 1 ≤ r) (hl : r ≤ L) (run : Runs (Calls A τ σ) r i [] (countWord u)) :=
    compile hb headi hr hτ hσ (show (i.length : ℝ)+r+2*σ+8 ≤ mainSpaceBound J b by
      have h := (hJ p (by omega)).1; have hi' : (i.length:ℝ) ≤ L := by exact_mod_cast hi
      have hr' : (r:ℝ) ≤ L := by exact_mod_cast hl
      change 2*(L:ℝ)+2*σ+8 ≤ _ at h; linarith) (hJ p (by omega)).2 run
  have ro := order _ _ _ (Query.ecOrder p h3 E)
  have oc : Calls A τ σ (tag9 0 (DetDLP_M3D_orderQuery i)) (encodeNatListBin [M]) := by
    apply liftCall A 0 (t:=mainSpaceBound k₀ b) (s:=polyBound k₀ b)
    · change RunsWithin S₀ o₀ _ _ _ _; simpa [i,M,b,DetDLP_M3D_orderQuery,DetDLP_M3D_curve,encodeECDLPInput,encodeCurveInput] using ro
    · exact ((hspace (by dsimp [v]; omega)).trans ss).trans hst
    · exact (hpoly (by dsimp [v]; omega)).trans ss
  constructor
  · intro small
    obtain ⟨u,hu,hr⟩ := scanTrace A E P Q small oc ((timeMono (by dsimp [k,v]; omega : k₁ ≤ k)).trans tt) ((hspace (by dsimp [v]; omega)).trans ss) (scan p h3 E P Q hg small)
    exact ⟨u,hu,machine (by decide) lens.2.1 hr⟩
  intro large F _
  obtain ⟨S,B,win,blocksOk,rp,re⟩ := plan p h3 E large.2.1 large.2.2
  refine ⟨S,B,blocksOk,?_⟩
  let FB := IndexedFactorBase.mk B
  let ctx := canonical E S B P Q
  let T := hashThreshold p (M-1) m M
  let enc := fun X : E.toAffine.Point => encodeNatListBin (pointCoords X)
  have hbl : ctx.blocks = BlockLookup.blocks FB enc := by simp [ctx,Context.blocks,canonical,encodeECFactorBlocks,BlockLookup.blocks,FB,enc,List.ofFn_eq_map,List.map_map,Function.comp_def]
  have hflat : ctx.blocks.flatten.length = FB.totalBaseSize := by rw [hbl]; exact ECQueryOps.baseLen FB
  have hsize : FB.totalCoords=ctx.size := by rw [Context.size,hflat]; rfl
  have hmod : ctx.modulus=M := by simp [ctx,Context.modulus,canonical,DetDLP_M3D_scalar,M]
  have hm : ctx.blocks.length=m := by simp [hbl,BlockLookup.blocks,m,b]
  have width : ctx.width=b := by simp [Context.width,ctx,canonical,primeField,inputFields,encodeECDLPInput,S8G.FpMoment.Code.width_eq,b]
  have depth : ctx.depth=4*m*(3*b) := by rw [Context.depth,hm,width]
  have hcurve : curveWord ctx.i=encodeCurveInput p E := by simp [ctx,canonical,curveWord,inputFields,encodeECDLPInput,encodeCurveInput]
  have cover := winningCover E h3 large S B win (fun i => (blocksOk i).2)
  have memB (i) (x : E.toAffine.Point) : x ∈ B i ↔ x ∈ m89_ec_plan_block E (some (T,S)) i := by rw [←List.mem_toFinset,(blocksOk i).2]; rfl
  have ok : m89_ec_plan_ok E (some (T,S)) := ⟨large.2.1,large.2.2,rfl,win⟩
  have decodeAt (j : Fin FB.totalCoords) := decode p h3 E (some (T,S)) ok (FB.elem P Q j) (by
    obtain ⟨a,b,h,eq⟩ := cover (FB.elem P Q j); exact ⟨a,b,fun t => ⟨(memB ..).1 (h t).1,(memB ..).1 (h t).2⟩,eq⟩)
  choose a e hmem hval runD using decodeAt
  have mem (j) (t) := And.intro ((memB ..).2 (hmem j t).1) ((memB ..).2 (hmem j t).2)
  let U (j) := indexed E B (a j) (e j) (mem j)
  have hU (j) : FB.tupleVal (U j)=FB.elem P Q j := (indexedVal E B _ _ _).trans (hval j)
  obtain ⟨z,zinit,zpass⟩ := recoverLabels (M:=M) Nat.card_eq_fintype_card P Q hg FB U hU
  let word (n : ℕ) := if h : n<FB.totalCoords then encodeECDecomp (a ⟨n,h⟩) (e ⟨n,h⟩) else []
  have decCall (j : ℕ) (hj : j<ctx.size) : Calls A τ σ (tag9 5 (ctx.decQ j)) (word j) := by
    let t : Fin FB.totalCoords := ⟨j,hsize.symm ▸ hj⟩
    have eq : ctx.decQ j = Encoding.encodeList id [Encoding.encodeList id [encodeCurveInput p E,enc (FB.elem P Q t)],m89_ec_plan_word (some (T,S))] := by
      have elem : elemWord ctx.i (BlockLookup.blocks FB enc) j = enc (FB.elem P Q t) := elemWord_correct FB P Q t
      have pw : planWord ctx.p = m89_ec_plan_word (some (T,S)) := by
        change (decodeFrames (Encoding.encodeList id [encodeCurveInput p E,m89_ec_plan_word (some (T,S))])).getD 1 [] = _
        rw [decodeFrames_correct]; rfl
      unfold Context.decQ; rw [hcurve,hbl,elem,pw]; rfl
    rw [eq]; dsimp only [word]; rw [dif_pos t.isLt]; exact liftCall A 5 (runD t) (((hspace (by dsimp [v]; omega)).trans ss).trans hst) ((hpoly (by dsimp [v]; omega)).trans ss)
  have nd (t) : ((FB.blocks t).map enc).Nodup := (blocksOk t).1.map encPoint_inj
  have nz : 0<M := prime.pos
  let q := nativeQ E S B P Q nz (w3_full M FB.totalCoords) []
  have bpow : p ≤ 2^b := Nat.le_pow_clog (by decide) p
  have hpow : 1 < 2^b := by omega
  have hNpos : 1 ≤ FB.totalCoords := by simp [IndexedFactorBase.totalCoords]
  have toBase {x : ℕ} {s : ℝ} (hx : x ≤ ⌊s⌋₊+8) (hs : s ≤ mainSpaceBound k b) : x+2 ≤ d := by
    have hh := Nat.floor_mono hs; dsimp [d,base]; omega
  have blimit := toBase (outLen re) (hspace (by dsimp [v]; omega))
  have Nlimit : FB.totalCoords ≤ d := by have := total_le B; change (IndexedFactorBase.mk B).totalBaseSize+2 ≤ d; omega
  have Mlimit : (countWord M).length ≤ d := by
    have hh := toBase (outLen ro) (hpoly (by dsimp [v]; omega)); change (encodeNatListBin [M]).length+2 ≤ d at hh
    have hh₁ : (countWord M).length+1 ≤ (encodeNatListBin [M]).length := w3_encodedMemberLength (enc:=countWord) List.mem_cons_self
    omega
  have Tlimit : (countWord T).length ≤ d := by
    have hh := toBase (outLen rp) (hpoly (by dsimp [v]; omega))
    have h₁ := w3_encodedMemberLength (enc:=id) (show countWord T ∈ [countWord T,List.ofFn (ecBits S)] by simp)
    have h₂ := w3_encodedMemberLength (enc:=id) (show m89_ec_plan_word (some (T,S)) ∈ [encodeCurveInput p E,m89_ec_plan_word (some (T,S))] by simp)
    change (Encoding.encodeList id [encodeCurveInput p E,m89_ec_plan_word (some (T,S))]).length+2 ≤ d at hh
    simp only [id_eq,m89_ec_plan_word,List.length_cons] at h₁ h₂ hh; omega
  have Mbits := (w3_clogWord M).trans Mlimit
  have short : FB.totalCoords + bitLen M ≤ L := (Nat.add_le_add Nlimit Mbits).trans lens.2.2.2.1
  have up (s : w3_Rep M FB.totalCoords) (r : w3_Row M FB.totalCoords) (inv : Invariant z s) (good : w3_holds r z) := updateCall A s r z inv good (update M _ prime.two_le hNpos s r) ((wide (by dsimp [v]; omega) (by omega : FB.totalCoords+bitLen M ≤ netLim k b+L)).trans hst) (wide (by dsimp [v]; omega) (by omega))
  have dispLarge : DetDLP_M3D_dispatch ctx.i ctx.o = true := by
    simpa [ctx,canonical,DetDLP_M3D_dispatch,DetDLP_M3D_scalar,encodeECDLPInput,NewtonPoly.largeCheck,S8G.FpMoment.Code.width_eq,S8G.FpMoment.Code.slots_eq,w3_large,M] using large
  have planCall : Calls A τ σ (tag9 2 (curveWord ctx.i)) ctx.p := by
    rw [hcurve]
    exact liftCall A 2 rp (((hspace (by dsimp [v]; omega)).trans ss).trans hst) ((hpoly (by dsimp [v]; omega)).trans ss)
  have enumCall : Calls A τ σ (tag9 3 ctx.p) ctx.k :=
    liftCall A 3 re (((hspace (by dsimp [v]; omega)).trans ss).trans hst) ((hspace (by dsimp [v]; omega)).trans ss)
  have genStep : ∃ t, w3_update ((w3_initRows FB M U)[0]'(by simp [w3_initRows])) (w3_full M FB.totalCoords) t ∧ Stage2Trace.Invariant z t ∧ Calls A τ σ (tag9 8 ctx.genQ) (repWord t) := by
    have hmem0 : (w3_unitRow FB M FB.genCoord, (1 : ZMod M)) ∈ w3_initRows FB M U := by simp [w3_initRows]
    obtain ⟨t, hu, hinv, _, hcall⟩ := up (w3_full M FB.totalCoords) (w3_unitRow FB M FB.genCoord, (1 : ZMod M)) (fullInv z) (zinit _ hmem0)
    have hgen : ctx.genQ = encodeCosetUpdateInput M (fun i : Fin FB.totalCoords => ((w3_full M FB.totalCoords).1 i).val) (w3_full M FB.totalCoords).2 (fun i => (w3_unitRow FB M FB.genCoord i).val) (1 : ZMod M).val := by
      unfold Context.genQ
      rw [hmod, ← hsize, hbl]
      simpa [w3_full] using genPacket FB M prime.one_lt
    exact ⟨t, hu, hinv, hgen.symm ▸ hcall⟩
  have initStep (j : ℕ) (hj : j < ctx.size) (s : w3_Rep M FB.totalCoords) (hs : Stage2Trace.Invariant z s) :
      ∃ t, w3_update ((w3_initRows FB M U)[j+1]'(by
        have hj' : j < FB.totalCoords := hsize.symm ▸ hj
        simpa only [w3_initRows,List.length_cons,List.length_map,List.length_finRange,Nat.succ_lt_succ_iff] using hj')) s t ∧
        Stage2Trace.Invariant z t ∧ Calls A τ σ (tag9 8 (ctx.updQ j (repWord s) (word j))) (repWord t) := by
    let idx : Fin FB.totalCoords := ⟨j, hsize.symm ▸ hj⟩
    have hjlt : j + 1 < (w3_initRows FB M U).length := by
      simpa only [w3_initRows,List.length_cons,List.length_map,List.length_finRange,Nat.succ_lt_succ_iff] using idx.isLt
    obtain ⟨t, hu, hinv, _, hcall⟩ := up s ((w3_initRows FB M U)[j+1]'hjlt) hs (zinit _ (List.getElem_mem hjlt))
    have hwd : BlockLookup.decodeFrames (word j) = BlockLookup.words FB enc (U idx) := by
      dsimp only [word]; rw [dif_pos idx.isLt]; exact indexedWord E B (a idx) (e idx) (mem idx)
    have hupd : ctx.updQ j (repWord s) (word j) = encodeCosetUpdateInput M (fun i => (s.1 i).val) s.2 (fun i => (((w3_initRows FB M U)[j+1]'hjlt).1 i).val) (((w3_initRows FB M U)[j+1]'hjlt).2).val := by
      unfold Context.updQ; rw [hmod, ← hsize, hbl, hwd]; exact initPacket FB M nd U idx s
    exact ⟨t, hu, hinv, hupd.symm ▸ hcall⟩
  have termAll (s : w3_Rep M FB.totalCoords) (f : Wd) :
      ∃ pkt res : Wd, f.length ≤ ctx.depth →
        Calls A τ σ (tag9 6 (ctx.query (repWord s) f)) pkt ∧
        Calls A τ σ (tag9 7 pkt) res ∧
        ∃ (C' : ℕ) (net : w3_Net (request ctx q s f) C'), pkt = w3_packet net ∧
          EncodesTruncPoly (w3_precision q) (w3_len q) res (BTNContract net.G net.T) := by
    by_cases hf : f.length ≤ ctx.depth
    · have hqs : w3_ecQueries (request ctx q s f) := nativeQ_valid E a₁ a₂ a₃ large S B blocksOk P Q s f nz
      obtain ⟨n, hbuild, _, res, henc, hcont⟩ := network (request ctx q s f) hqs
      have hBlen : (encodeECFactorBlocks B).length ≤ d := by omega
      have hqlen : (request ctx q s f).input.length ≤ L :=
        queryLen E S B P Q (fun j => (s.1 j).val) s.2 f k lens.2.2.2.2 Nlimit hBlen Mlimit Tlimit (fun j => ZMod.val_lt (s.1 j)) (depth ▸ hf)
      have hbcall : Calls A τ σ (tag9 6 (ctx.query (repWord s) f)) (w3_packet n) :=
        liftCall A 6 hbuild (((wide (by dsimp [v]; omega) (by omega : (request ctx q s f).input.length ≤ netLim k b + L)).trans hst)) (wide (by dsimp [v]; omega) (by omega))
      have hpkt : (w3_packet n).length ≤ ⌊polyBound g (request ctx q s f).input.length⌋₊ + 8 := outLen hbuild
      have hpolg : ⌊polyBound g (request ctx q s f).input.length⌋₊ ≤ pol k L := by
        have hp1 : polyBound g (request ctx q s f).input.length ≤ (pol k L : ℝ) := by
          rw [pol_eq]; exact polyMono (by dsimp [k, v]; omega) hqlen
        simpa using Nat.floor_mono hp1
      have hdesc : n.desc.length + 1 ≤ (w3_packet n).length :=
        w3_encodedMemberLength (enc:=id) (xs := [n.desc, n.G.encode, countWord (request ctx q s f).b, countWord (request ctx q s f).m, countWord (request ctx q s f).k, countWord n.S, countWord (w3_precision (request ctx q s f)), countWord (w3_len (request ctx q s f)), _]) List.mem_cons_self
      have hSbound : n.S ≤ k * L ^ 2 := by
        have hs1 : n.S ≤ c * m * b := n.shape.2.2.2.2.2.1
        have hc : c ≤ k := by dsimp [k, v]; omega
        have hmL : m ≤ L := lens.2.2.2.2.trans (by have := lens.2.2.2.1; omega)
        have hbL : b ≤ L := lens.2.2.1
        calc n.S ≤ c * m * b := hs1
          _ ≤ k * L * L := Nat.mul_le_mul (Nat.mul_le_mul hc hmL) hbL
          _ = k * L ^ 2 := by ring
      have hSD : n.S + n.desc.length ≤ netLim k b := by
        dsimp [netLim, L] at *; omega
      have hsp7 : polyBound k₇ (n.S + n.desc.length) ≤ σ :=
        wide (by dsimp [v]; omega) (by omega : n.S + n.desc.length ≤ netLim k b + L)
      have htm7 : polyBound k₇ (n.S + n.desc.length) * mainTimeBound k₇ b ≤ τ := by
        have ht1 : mainTimeBound k₇ b ≤ mainTimeBound k b := timeMono (by dsimp [k, v]; omega)
        have hm1 : polyBound k₇ (n.S + n.desc.length) * mainTimeBound k₇ b ≤ σ * mainTimeBound k b :=
          mul_le_mul hsp7 ht1 (by unfold mainTimeBound; positivity) hσ
        dsimp [τ, timeB]; nlinarith
      have hccall : Calls A τ σ (tag9 7 (w3_packet n)) res := liftCall A 7 hcont htm7 hsp7
      exact ⟨w3_packet n, res, fun _ => ⟨hbcall, hccall, c, n, rfl, henc⟩⟩
    · exact ⟨[], [], fun h => False.elim (hf h)⟩
  choose packets results termSpec using termAll
  have updSpec (s : w3_Rep M FB.totalCoords) (hs : Invariant z s) (X Y : FB.BlockTuple)
      (hXY : FB.tupleVal Y = FB.tupleVal X + P) (hviol : ¬w3_holds (w3_shiftRow FB M X Y) s.1) :
      ∃ t, w3_update (w3_shiftRow FB M X Y) s t ∧ 2 * Nat.card (w3_coset t) ≤ Nat.card (w3_coset s) ∧
        Calls A τ σ (tag9 8 (ctx.cutQ (repWord s) (q.code X Y))) (repWord t) := by
    obtain ⟨t, hu, _, hhalf, hcall⟩ := up s (w3_shiftRow FB M X Y) hs (zpass X Y hXY)
    have hcut : ctx.cutQ (repWord s) (q.code X Y) = encodeCosetUpdateInput M (fun i => (s.1 i).val) s.2 (fun i => ((w3_shiftRow FB M X Y).1 i).val) ((w3_shiftRow FB M X Y).2).val := by
      unfold Context.cutQ; rw [hmod, ← hsize, width, hm, hbl]
      exact shiftPacket FB M nd b hpow bpow prime.one_lt s X Y
    exact ⟨t, hu, hhalf hviol, hcut.symm ▸ hcall⟩
  have htarget : FB.targetCoord.val = ctx.blocks.flatten.length + 1 := by
    rw [hflat]; rfl
  obtain ⟨y, n, hout, hn, hrun⟩ := m3d_ec_trace_protocol.2 ctx q z (Calls A τ σ) U hsize rfl dispLarge oc planCall enumCall word decCall genStep initStep hm hmod prime.two_le htarget (fun X Y => (tupleCode_width FB b X Y).trans depth.symm) (tupleCode_inj FB (fun i => (blocksOk i).1) b hpow bpow) packets results termSpec updSpec zpass
  have hfuel : 2 + n * (2 * ctx.depth + 3) + 2 * ctx.size + 5 ≤ L := by
    rw [depth, ← hsize]; exact fuelBound lens.2.2.2.2 Nlimit Mbits hn
  have hacc := machine (by omega) hfuel hrun
  refine ⟨?_, U, y, hU, hout, hacc⟩
  rintro _ ⟨X, rfl⟩
  obtain ⟨a₀, e₀, h₀, eq₀⟩ := cover ((IndexedFactorBase.mk F).tupleVal X)
  exact ⟨indexed E B a₀ e₀ h₀, (indexedVal E B a₀ e₀ h₀).trans eq₀⟩

end
end DetDLP.M3D.Fast.ECRun.Assembly

open DetDLP
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem solution
    (hord : DetDLP.M89S1.CountOracle)
    (en : PrimitiveMachine) (eo : Fin en.tapeCount) (de : PrimitiveMachine) (do' : Fin de.tapeCount) (K : ℕ)
    (hnet : w3_terminalOps w3_ecQueries) (hupdate : w3_hnfOps) :
    ∃ (D : PrimitiveMachine) (out : Fin D.tapeCount) (C : ℕ),
      ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
        E.a₁ = 0 → E.a₂ = 0 → E.a₃ = 0 →
        letI := ecPointFintype E
        let M := Fintype.card E.toAffine.Point
        let m := blockCount (bitLen p)
        M.Prime → ∀ (P Q : E.toAffine.Point), addOrderOf P = M →
          let accepts := fun u => RunsWithin D out (encodeECDLPInput p E P Q) (countWord u)
                                    (mainTimeBound C (bitLen p)) (mainSpaceBound C (bitLen p))
          (¬ w3_large p M → w3_scanOutput M P Q accepts) ∧
          (w3_large p M → ∀ F : Fin m → List E.toAffine.Point, w3_ecBaseCalls en eo de do' K E F →
            ∃ (seed : ECSeed p m) (B : Fin m → List E.toAffine.Point),
              (∀ i, (B i).Nodup ∧ (B i).toFinset = ecFactorBlock E (hashThreshold p (M-1) m M) seed i) ∧
              w3_traceOutput ⟨F⟩ ⟨B⟩ M P Q accepts) :=
  DetDLP.M3D.Fast.ECRun.Assembly.driver hord en eo de do' K hnet hupdate


