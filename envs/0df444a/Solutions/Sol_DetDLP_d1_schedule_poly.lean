-- Prove2me | solution 1 for DetDLP.d1_schedule_poly
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T06:25:08.226327+00:00
-- url     : https://prove2.me/submissions/3747246f-74d9-4c81-9f0d-6a2d2f242f33

import Definitions.Def_DetDLP_D1Schedule
import Theorems.Thm_DetDLP_d1_exact_radius_scan_poly
import Theorems.Thm_Groundwork_PolyT_pow_unary
import Theorems.Thm_Groundwork_Unary_of_length
import Theorems.Thm_Groundwork_Unary_of_le
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_sum
set_option autoImplicit false
namespace DetDLP.D1
open AppendixD4 Groundwork Groundwork.PolyT DetDLP_W1_Queries
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

private theorem peak_le (ns : List ℕ) (a k : ℕ) : ns.foldl max a ≤ k ↔ a ≤ k ∧ ∀ n ∈ ns, n ≤ k := by
  induction ns generalizing a with
  | nil => simp
  | cons n ns ih => simp [ih,max_le_iff,and_assoc]

private theorem flat_count (G : BipartiteMultigraph) (v : Fin G.nV) (es : List (Fin G.nE)) :
    (es.flatMap fun e => [(G.endpoints e).1.val,(G.endpoints e).2.val]).count v.val =
      (es.filter fun e => decide ((G.endpoints e).1 = v ∨ (G.endpoints e).2 = v)).length := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have hn : (G.endpoints e).1 ≠ (G.endpoints e).2 := fun h => G.bipartite e (congrArg G.side h)
    by_cases h : (G.endpoints e).1 = v <;> by_cases h' : (G.endpoints e).2 = v
    · exact (hn (h.trans h'.symm)).elim
    all_goals simp [List.count_cons, List.flatMap_cons, ih, ← Fin.ext_iff,h,h']

private theorem degree_spec (G : BipartiteMultigraph) : degreeRaw G.encode = G.maxDeg := by
  simp only [degreeRaw, field4, BipartiteMultigraph.encode,third,second,more_cons,first_cons,
    id_eq,List.length_ofFn,w5_M6Sort.decode_encode,peak,BipartiteMultigraph.maxDeg]
  apply le_antisymm
  · rw [peak_le]; refine ⟨by omega,?_⟩
    intro n hn; obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hn
    let w : Fin G.nV := ⟨v,List.mem_range.mp hv⟩
    exact (flat_count G w _).le.trans (Finset.le_sup (f:=G.deg) (Finset.mem_univ w))
  · refine Finset.sup_le fun v _ => ?_
    apply ((peak_le _ 0 _).mp le_rfl).2
    exact List.mem_map.mpr ⟨v.val,List.mem_range.mpr v.isLt,flat_count G v _⟩

private theorem xs (D : ℕ) (f : ℕ → ℕ) : (List.range D).map f = List.ofFn (fun d : Fin D => f d.val) := by
  apply List.ext_getElem <;> simp

private theorem polyX : polynomialBits (Polynomial.X : Polynomial ℤ) = [false] := by
  apply List.ext_getElem <;> simp [polynomialBits]

private theorem core_spec (C b e deg : ℕ) : scheduleCore C b e deg = (makeSchedule C b e deg).bits Polynomial.X := by
  let r := radiusScan (b,deg)
  let H := horizon b r
  let m := C*b
  let D := depth m H
  let us := widths m r D
  change (if r < threshold C ∨ e ≤ H then scheduleWord e 0 0 1 [] [] else
    scheduleWord H D (b/2^r) (kappa m) us ((List.range D).map (shift us))) =
    (if r < threshold C ∨ e ≤ H then trivialSchedule e else fullSchedule b r m H).bits Polynomial.X
  by_cases h : r < threshold C ∨ e ≤ H
  · rw [if_pos h,if_pos h]; simp only [scheduleWord,trivialSchedule,Schedule.bits,polyX,List.ofFn_zero]
  · rw [if_neg h,if_neg h]; change scheduleWord H D _ _ us _ = (fullSchedule b r m H).bits _
    dsimp only [fullSchedule,Schedule.bits,scheduleWord]; rw [polyX]
    simp only [us,widths,xs,D]

private theorem raw_spec (C b P l : ℕ) (desc : List Bool) (G : BipartiteMultigraph) :
    scheduleRaw C (encodeBTNInstance desc G b P l) = (makeSchedule C b G.nE G.maxDeg).bits Polynomial.X := by
  simp only [scheduleRaw,encodeBTNInstance,third,second,more_cons,first_cons,id_eq,decode_count,degree_spec]
  simp only [BipartiteMultigraph.encode,more_cons,first_cons,id_eq,decode_count]
  exact core_spec ..

attribute [local fun_prop] Groundwork.PolyT.comp Groundwork.PolyT.const Groundwork.PolyT.fst Groundwork.PolyT.snd
  Groundwork.PolyT.prodMk Groundwork.PolyT.map Groundwork.PolyT.filter Groundwork.PolyT.count Groundwork.PolyT.sum
  Groundwork.PolyT.mul Groundwork.PolyT.div Groundwork.PolyT.length P2M_Groundwork_PolyT_cons__3a60f43a3b86
  P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_ite__226169acf219
  first_poly more_poly frame_poly w5_M6Sort.encode_poly

variable {α : Type} [Enc α]
private theorem fuelU {m : α → ℕ} (hm : PolyT m) : Unary (fun x => fuel (m x)) := by
  exact Unary.of_length (P2M_Groundwork_PolyT_cons__3a60f43a3b86 (Groundwork.PolyT.const false) (bits hm))

private theorem radU {b de : α → ℕ} (hb : PolyT b) (he : PolyT de) : Unary (fun x => radiusScan (b x,de x)) := by
  have hp := d1_exact_radius_scan_poly.2.comp (prodMk hb he)
  apply (fuelU hb).of_le hp
  intro x
  simpa [radiusScan,fuel] using List.length_filter_le (scanTest (b x) (de x)) (List.range (fuel (b x)))

private theorem depthListP {m H : α → ℕ} (hm : PolyT m) (hH : PolyT H) :
    PolyT (fun x => (List.range (fuel (m x))).filter fun d => decide (H x < m x / 8^(min d (fuel (m x))))) := by
  apply filter (l:=fun x => List.range (fuel (m x)))
  · have hmu : PolyT (fun x : α × ℕ => m x.1) := hm.comp (by fun_prop)
    have hmin := (fuelU hmu).of_le (f:=fun x : α × ℕ => min x.2 (fuel (m x.1))) (by unfold fuel; fun_prop) (fun _ => min_le_right ..)
    have hp := pow_unary (Groundwork.PolyT.const 8) hmin
    fun_prop
  · exact range (fuelU hm)

private theorem peakP : PolyT peak := by
  apply foldl_add (l:=fun ns : List ℕ => ns) (a:=fun _ => 0) (g:=fun _ a b => max a b) (by fun_prop) (by fun_prop) (by fun_prop)
  refine ⟨id,PB.id',?_⟩
  intro ns a b hb
  rcases le_total a b with h|h <;> simp [max_eq_right,max_eq_left,h,Groundwork.len_le_of_mem hb] <;> have := len_le_of_mem hb <;> omega

private theorem degreeP : PolyT degreeRaw := by
  unfold degreeRaw field4 third second
  apply peakP.comp
  apply Groundwork.PolyT.map (f:=fun g v => (w5_M6Sort.decode _).count v)
  · apply Groundwork.PolyT.count (by fun_prop)
    apply w5_M6Sort.decode_poly.comp; fun_prop
  · apply range; apply Unary.of_length; fun_prop

private theorem wordP {h d cp k : α → ℕ} {u a : α → List ℕ} (hh : PolyT h) (hd : PolyT d) (hcp : PolyT cp)
    (hk : PolyT k) (hu : PolyT u) (ha : PolyT a) : PolyT (fun x => scheduleWord (h x) (d x) (cp x) (k x) (u x) (a x)) := by
  simp only [scheduleWord,Encoding.encodeList,id_eq,← frame_correct]
  fun_prop

set_option maxHeartbeats 1200000 in
private theorem coreP (C : ℕ) {b ne de : α → ℕ} (hb : PolyT b) (hn : PolyT ne) (he : PolyT de) :
    PolyT (fun x => scheduleCore C (b x) (ne x) (de x)) := by
  let r := fun x => radiusScan (b x,de x)
  have hru : Unary r := radU hb he
  have hr : PolyT r := d1_exact_radius_scan_poly.2.comp (prodMk hb he)
  let H := fun x => horizon (b x) (r x)
  have hroot : PolyT (fun x => rootScan (r x)) := by
    unfold rootScan; apply Groundwork.PolyT.length
    apply filter (l:=fun x => List.range (r x)) _ (range hru)
    have hrp : PolyT (fun p : α × ℕ => r p.1) := hr.comp (by fun_prop)
    have hj : PolyT (fun p : α × ℕ => p.2+1) := by fun_prop
    exact decide_le (Groundwork.PolyT.mul hj hj) hrp
  have hH : PolyT H := by dsimp [H,horizon]; fun_prop
  let m := fun x => C*b x
  have hm : PolyT m := by dsimp [m]; fun_prop
  let D := fun x => depth (m x) (H x)
  have hDu : Unary D := Unary.of_length (depthListP hm hH)
  have hD : PolyT D := Groundwork.PolyT.length (depthListP hm hH)
  let us := fun x => widths (m x) (r x) (D x)
  have hus : PolyT us := by
    apply Groundwork.PolyT.map (f:=fun x j => width (m x) (r x) j) _ (range hDu)
    have hmu : PolyT (fun x : α × ℕ => m x.1) := hm.comp (by fun_prop)
    have hu := (fuelU hmu).of_le (f:=fun x : α × ℕ => min x.2 (fuel (m x.1))) (by unfold fuel; fun_prop) (fun _ => min_le_right ..)
    have hp := pow_unary (Groundwork.PolyT.const 2) hu
    exact Groundwork.PolyT.div (Groundwork.PolyT.div (hr.comp (by fun_prop)) (Groundwork.PolyT.const 131072)) hp
  have has : PolyT (fun x => (List.range (D x)).map (shift (us x))) := by
    apply Groundwork.PolyT.map (f:=fun x j => shift (us x) j) _ (range hDu); unfold shift; fun_prop
  have hcap := Groundwork.PolyT.div hb (pow_unary (Groundwork.PolyT.const 2) hru)
  have ht := wordP hn (Groundwork.PolyT.const 0) (Groundwork.PolyT.const 0) (Groundwork.PolyT.const 1) (Groundwork.PolyT.const []) (Groundwork.PolyT.const [])
  have hf := wordP hH hD hcap (k:=fun x => kappa (m x)) (by unfold kappa; fun_prop) hus has
  change PolyT (fun x => if r x < threshold C ∨ ne x ≤ H x then _ else _)
  fun_prop

private theorem rawP (C : ℕ) : PolyT (scheduleRaw C) := by
  unfold scheduleRaw; apply coreP
  · unfold third second; fun_prop
  · unfold second; fun_prop
  · apply degreeP.comp; unfold second; fun_prop

end DetDLP.D1

open DetDLP DetDLP.D1
theorem solution : ∀ C : ℕ, 0 < C → Groundwork.PolyT (scheduleRaw C) ∧ ∀ (b P l : ℕ) (desc : List Bool) (G : BipartiteMultigraph),
  scheduleRaw C (encodeBTNInstance desc G b P l) = (makeSchedule C b G.nE G.maxDeg).bits Polynomial.X :=
  fun C _ => ⟨D1.rawP C,D1.raw_spec C⟩
