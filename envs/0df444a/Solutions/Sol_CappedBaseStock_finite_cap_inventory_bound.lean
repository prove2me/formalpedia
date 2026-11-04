-- Prove2me | solution 1 for CappedBaseStock.finite_cap_inventory_bound
-- status  : ACCEPTED   (prove)
-- author  : @StellaXin
-- created : 2026-09-08T02:36:58.86821+00:00
-- url     : https://prove2.me/submissions/46bbe2eb-7db3-4c4a-8d62-b810ac623afe

import Definitions.Def_CappedBaseStock_Model

/-! Direct proof of the finite-cap inventory moment bound.
Pathwise capacity and inventory envelopes are combined with the actual i.i.d.
demand law. Every supporting lemma below is proved in this file. -/


noncomputable section
open scoped NNReal ENNReal BigOperators
open CappedBaseStock
namespace CappedBaseStockBounds

def position {L : ℕ} (s : State L) : ℝ≥0 := s.1 + ∑ i : Fin L, s.2 i

lemma shift_sum (n : ℕ) (f : Fin (n+1) → ℝ≥0) (q : ℝ≥0) :
    (∑ i : Fin (n+1), if hi : i.val + 1 < n+1 then f ⟨i.val+1, hi⟩ else q)
      + f 0 = (∑ i : Fin (n+1), f i) + q := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  simp [Fin.succ, add_comm, add_left_comm, add_assoc]

lemma pipelineSum_step (c : Parameters) (s : State c.L) (q d : ℝ≥0) :
    (∑ i : Fin c.L, (step c s q d).2 i) + arrival c s =
      (∑ i : Fin c.L, s.2 i) + q := by
  rcases c with ⟨L, hL, h, p, hh, hp⟩
  cases L with
  | zero => omega
  | succ n => simpa [step, arrival] using shift_sum n s.2 q

lemma position_step (c : Parameters) (s : State c.L) (q d : ℝ≥0) :
    position (step c s q d) + filledDemand c s d = position s + q := by
  have hs := pipelineSum_step c s q d
  have hfilled : s.1 + arrival c s - d + min d (s.1 + arrival c s) =
      s.1 + arrival c s := by
    simpa [min_comm] using (tsub_add_min (a := s.1 + arrival c s) (b := d))
  simp only [position, step, filledDemand]
  simpa only [step] using (by linear_combination hs + hfilled :
    s.1 + arrival c s - d +
      (∑ i : Fin c.L, (step c s q d).2 i) + min d (s.1 + arrival c s) =
    s.1 + (∑ i : Fin c.L, s.2 i) + q)

lemma cbsOrder_le_cap (L : ℕ) (S r : ℝ≥0) (s : State L) :
    cbsOrder L S r s ≤ r := min_le_right _ _

lemma position_add_order_le (L : ℕ) (S r : ℝ≥0) (s : State L)
    (hs : position s ≤ S) : position s + cbsOrder L S r s ≤ S := by
  calc
    position s + cbsOrder L S r s ≤ position s + (S - position s) := by
      exact add_le_add le_rfl (min_le_left (S - position s) r)
    _ = S := add_tsub_cancel_of_le hs

lemma cbsRun_position_le (c : Parameters) (S r : ℝ≥0) (ω : Sample) (t : ℕ) :
    position (cbsRun c S r ω t) ≤ S := by
  induction t with
  | zero => simp [cbsRun, initialState, position]
  | succ t ih =>
      have hp := position_step c (cbsRun c S r ω t)
        (cbsOrder c.L S r (cbsRun c S r ω t)) (ω.1 t)
      have hb := position_add_order_le c.L S r (cbsRun c S r ω t) ih
      rw [← hp] at hb
      exact (le_add_right le_rfl).trans hb

lemma cbsRun_slot (c : Parameters) (S r : ℝ≥0) (ω : Sample) (t : ℕ)
    (i : Fin c.L) :
    (cbsRun c S r ω t).2 i = if t + i.val < c.L then 0 else
      cbsOrder c.L S r (cbsRun c S r ω (t + i.val - c.L)) := by
  induction t generalizing i with
  | zero => simp [cbsRun, initialState, i.isLt]
  | succ t ih =>
      simp only [cbsRun, step]
      split_ifs with hi ht
      · rw [ih]
        split_ifs <;> simp_all <;> omega
      · rw [ih]
        split_ifs <;> simp_all
        · omega
        · congr 3 <;> omega
      · omega
      · have hi' : i.val + 1 = c.L := by omega
        congr 3
        omega

lemma cbsRun_arrival (c : Parameters) (S r : ℝ≥0) (ω : Sample) (t : ℕ) :
    arrival c (cbsRun c S r ω t) = if t < c.L then 0 else
      cbsOrder c.L S r (cbsRun c S r ω (t - c.L)) := by
  simpa [arrival] using cbsRun_slot c S r ω t
    ⟨0, lt_of_lt_of_le Nat.zero_lt_one c.leadTime_pos⟩

lemma cbsRun_pipeline_le (c : Parameters) (S r : ℝ≥0) (ω : Sample) (t : ℕ)
    (i : Fin c.L) : (cbsRun c S r ω t).2 i ≤ r := by
  rw [cbsRun_slot]
  split_ifs
  · exact zero_le
  · exact cbsOrder_le_cap _ _ _ _

lemma cbsRun_arrival_le (c : Parameters) (S r : ℝ≥0) (ω : Sample) (t : ℕ) :
    arrival c (cbsRun c S r ω t) ≤ r := by
  exact cbsRun_pipeline_le _ _ _ _ _ _

lemma cbsRun_inventory_le (c : Parameters) (S r : ℝ≥0) (ω : Sample) (t : ℕ) :
    (cbsRun c S r ω t).1 ≤ S := by
  exact (le_add_right le_rfl).trans (cbsRun_position_le c S r ω t)

lemma cbsRun_future_arrival (c : Parameters) (S r : ℝ≥0) (ω : Sample)
    (t : ℕ) (i : Fin c.L) :
    arrival c (cbsRun c S r ω (t + i.val)) = (cbsRun c S r ω t).2 i := by
  rw [cbsRun_arrival, cbsRun_slot]

lemma cbsRun_arrival_after_leadTime (c : Parameters) (S r : ℝ≥0) (ω : Sample)
    (t : ℕ) : arrival c (cbsRun c S r ω (t + c.L)) =
      cbsOrder c.L S r (cbsRun c S r ω t) := by
  rw [cbsRun_arrival]
  simp

lemma cbsRun_block_resources (c : Parameters) (S r : ℝ≥0) (ω : Sample) (t : ℕ) :
    (cbsRun c S r ω t).1 +
      (∑ j ∈ Finset.range (c.L + 1), arrival c (cbsRun c S r ω (t+j))) ≤ S := by
  rw [Finset.sum_range_succ, cbsRun_arrival_after_leadTime]
  have hsum : (∑ j ∈ Finset.range c.L, arrival c (cbsRun c S r ω (t+j))) =
      ∑ i : Fin c.L, (cbsRun c S r ω t).2 i := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun i _ => cbsRun_future_arrival c S r ω t i)
  rw [hsum, ← add_assoc]
  exact position_add_order_le _ _ _ _ (cbsRun_position_le c S r ω t)

lemma cbsRun_slot_sum (c : Parameters) (S r : ℝ≥0) (ω : Sample)
    (N : ℕ) (i : Fin c.L) :
    (∑ t ∈ Finset.range N, (cbsRun c S r ω t).2 i) =
      ∑ t ∈ Finset.range (N + i.val - c.L),
        cbsOrder c.L S r (cbsRun c S r ω t) := by
  induction N with
  | zero => simp [Nat.sub_eq_zero_of_le (Nat.le_of_lt i.isLt)]
  | succ N ih =>
      rw [Finset.sum_range_succ, cbsRun_slot, ih]
      by_cases h : N + i.val < c.L
      · have hN : N + i.val - c.L = 0 := by omega
        have hN' : N + 1 + i.val - c.L = 0 := by omega
        simp [h, hN, hN']
      · rw [if_neg h, show N + 1 + i.val - c.L = (N + i.val - c.L) + 1 by omega,
          Finset.sum_range_succ]

lemma cbsRun_pipeline_sum_le (c : Parameters) (S r : ℝ≥0) (ω : Sample) (N : ℕ) :
    (∑ t ∈ Finset.range N, ∑ i : Fin c.L, (cbsRun c S r ω t).2 i) ≤
      (c.L : ℝ≥0) * ∑ t ∈ Finset.range N, cbsOrder c.L S r (cbsRun c S r ω t) := by
  rw [Finset.sum_comm]
  calc
    (∑ i : Fin c.L, ∑ t ∈ Finset.range N, (cbsRun c S r ω t).2 i) ≤
        ∑ _i : Fin c.L, ∑ t ∈ Finset.range N,
          cbsOrder c.L S r (cbsRun c S r ω t) := by
      apply Finset.sum_le_sum
      intro i _
      rw [cbsRun_slot_sum]
      exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
    _ = _ := by simp

lemma cbsRun_inventory_zero_initial (c : Parameters) (S r : ℝ≥0) (ω : Sample)
    (t : ℕ) (ht : t ≤ c.L) : (cbsRun c S r ω t).1 = 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have hi := ih (by omega)
      have ha : arrival c (cbsRun c S r ω t) = 0 := by
        rw [cbsRun_arrival, if_pos (by omega)]
      simp only [cbsRun, step, hi, ha, zero_add, zero_tsub]

end CappedBaseStockBounds


open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace CappedBaseStockBounds
open CappedBaseStock

def reversePrefixIndex (t i : ℕ) : ℕ := if i ≤ t then t - i else i

lemma reversePrefixIndex_injective (t : ℕ) : Function.Injective (reversePrefixIndex t) := by
  intro i j h
  unfold reversePrefixIndex at h
  split_ifs at h <;> omega

lemma measurePreserving_reindex (P : DemandLaw) (f : ℕ → ℕ) (hf : Function.Injective f) :
    MeasurePreserving (fun d : DemandPath => fun i => d (f i))
      (demandPathLaw P) (demandPathLaw P) := by
  constructor
  · fun_prop
  · exact Measure.map_infinitePi_infinitePi_of_inj hf

lemma measurePreserving_sample_reindex (P : DemandLaw) (f : ℕ → ℕ)
    (hf : Function.Injective f) :
    MeasurePreserving (fun ω : Sample => fun i => ω.1 (f i))
      (sampleLaw P) (demandPathLaw P) := by
  exact (measurePreserving_reindex P f hf).comp measurePreserving_fst

lemma lintegral_sample_reindex (P : DemandLaw) (f : ℕ → ℕ)
    (hf : Function.Injective f) (F : DemandPath → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω, F (fun i => ω.1 (f i)) ∂sampleLaw P) =
      ∫⁻ d, F d ∂demandPathLaw P := by
  exact (measurePreserving_sample_reindex P f hf).lintegral_comp hF

lemma integral_sample_reindex (P : DemandLaw) (f : ℕ → ℕ)
    (hf : Function.Injective f) (F : DemandPath → ℝ) (hF : Measurable F) :
    (∫ ω, F (fun i => ω.1 (f i)) ∂sampleLaw P) =
      ∫ d, F d ∂demandPathLaw P := by
  have hm := measurePreserving_sample_reindex P f hf
  rw [← integral_map hm.measurable.aemeasurable hF.aestronglyMeasurable, hm.map_eq]

lemma integrable_sample_reindex (P : DemandLaw) (f : ℕ → ℕ)
    (hf : Function.Injective f) (F : DemandPath → ℝ)
    (hF : Integrable F (demandPathLaw P)) :
    Integrable (fun ω => F (fun i => ω.1 (f i))) (sampleLaw P) := by
  exact (measurePreserving_sample_reindex P f hf).integrable_comp_of_integrable hF

end CappedBaseStockBounds

noncomputable section
open scoped BigOperators
namespace CappedBaseStockBounds
lemma lindley_terminal_bound (u a : ℕ → ℝ) (n : ℕ) (B : ℝ)
    (hstep : ∀ t < n, u (t + 1) ≤ max (u t + a t) 0)
    (hinit : u 0 + ∑ i ∈ Finset.range n, a i ≤ B)
    (htail : ∀ k, 1 ≤ k → k ≤ n → ∑ i ∈ Finset.Ico k n, a i ≤ B) :
    u n ≤ B := by
  have haux : ∀ t, t ≤ n →
      u t ≤ B - (∑ i ∈ Finset.range n, a i) + ∑ i ∈ Finset.range t, a i := by
    intro t
    induction t with
    | zero =>
        intro _
        simp only [Finset.range_zero, Finset.sum_empty]
        linarith
    | succ t ih =>
        intro ht
        have ht0 : t < n := by omega
        have hi := ih (by omega)
        have hs := htail (t + 1) (by omega) ht
        rw [Finset.sum_Ico_eq_sub _ ht] at hs
        apply (hstep t ht0).trans
        apply max_le
        · rw [Finset.sum_range_succ]
          linarith
        · linarith
  have h := haux n le_rfl
  linarith


end CappedBaseStockBounds


noncomputable section
open scoped NNReal ENNReal BigOperators
open CappedBaseStock
namespace CappedBaseStockBounds

lemma sum_reverse_Ico (f : ℕ → ℝ) (m k : ℕ) (hk : k ≤ m) :
    (∑ i ∈ Finset.Ico k m, f i) =
      ∑ j ∈ Finset.range (m-k), f (m-1-j) := by
  apply Finset.sum_bij (fun i _ => m-1-i)
  · intro i hi
    simp only [Finset.mem_Ico] at hi
    simp only [Finset.mem_range]
    omega
  · intro i hi j hj hij
    simp only [Finset.mem_Ico] at hi hj
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    refine ⟨m-1-j, ?_, ?_⟩
    · simp only [Finset.mem_Ico]
      omega
    · omega
  · intro i hi
    simp only [Finset.mem_Ico] at hi
    congr 1
    omega

lemma inventory_window_bound (u A : ℕ → ℝ) (d rev : DemandPath)
    (m : ℕ) (r z : ℝ)
    (hstep : ∀ i < m, u (i+1) ≤ max (u i + A i - (d i : ℝ)) 0)
    (hcap : ∀ i < m, A i ≤ r)
    (hresources : u 0 + ∑ i ∈ Finset.range m, A i ≤ (m : ℝ)*r+z)
    (hrev : ∀ i < m, rev i = d (m-1-i)) :
    u m ≤ max (finiteInventory rev r m)
      (z - ∑ i ∈ Finset.range m, ((rev i : ℝ)-r)) := by
  have hsum : (∑ i ∈ Finset.range m, ((d i : ℝ)-r)) =
      ∑ i ∈ Finset.range m, ((rev i : ℝ)-r) := by
    rw [← Nat.Ico_zero_eq_range, sum_reverse_Ico _ m 0 (Nat.zero_le _)]
    simp only [Nat.sub_zero, Nat.Ico_zero_eq_range]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hrev i (Finset.mem_range.mp hi)]
  apply lindley_terminal_bound u (fun i => A i - (d i : ℝ)) m
  · intro i hi
    simpa only [sub_eq_add_neg, add_assoc] using hstep i hi
  · apply le_trans _ (le_max_right _ _)
    rw [← hsum]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    linarith
  · intro k hk hkm
    apply le_trans _ (le_max_left _ _)
    calc
      (∑ i ∈ Finset.Ico k m, (A i - (d i : ℝ))) ≤
          ∑ i ∈ Finset.Ico k m, (r - (d i : ℝ)) := by
        apply Finset.sum_le_sum
        intro i hi
        exact sub_le_sub_right (hcap i (Finset.mem_Ico.mp hi).2) _
      _ = ∑ i ∈ Finset.range (m-k), (r - (rev i : ℝ)) := by
        rw [sum_reverse_Ico _ m k hkm]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hrev i (by have := Finset.mem_range.mp hi; omega)]
      _ ≤ finiteInventory rev r m := by
        exact Finset.le_sup' (fun j => ∑ i ∈ Finset.range j, (r - (rev i : ℝ)))
          (Finset.mem_range.mpr (by omega))

lemma cbsRun_inventory_envelope (c : Parameters) (r z : ℝ)
    (hr : 0 ≤ r) (hz : 0 ≤ z) (ω : Sample) (t : ℕ) (ht : c.L ≤ t) :
    let S := Real.toNNReal (((c.L : ℝ)+1)*r+z)
    let rev : DemandPath := fun i => ω.1 (reversePrefixIndex t i)
    ((cbsRun c S (Real.toNNReal r) ω (t+1)).1 : ℝ) ≤
      max (finiteInventory rev r (c.L+1))
        (z - ∑ i ∈ Finset.range (c.L+1), ((rev i : ℝ)-r)) := by
  dsimp only
  let S := Real.toNNReal (((c.L : ℝ)+1)*r+z)
  let R := Real.toNNReal r
  have hS : (S : ℝ) = ((c.L : ℝ)+1)*r+z := by
    apply Real.coe_toNNReal
    positivity
  have hR : (R : ℝ) = r := Real.coe_toNNReal r hr
  have hend : t - c.L + (c.L+1) = t+1 := by omega
  have hbound := inventory_window_bound
    (fun i => ((cbsRun c S R ω (t-c.L+i)).1 : ℝ))
    (fun i => (arrival c (cbsRun c S R ω (t-c.L+i)) : ℝ))
    (fun i => ω.1 (t-c.L+i)) (fun i => ω.1 (reversePrefixIndex t i))
    (c.L+1) r z ?_ ?_ ?_ ?_
  · simpa only [hend] using hbound
  · intro i hi
    have heq : t-c.L+(i+1) = (t-c.L+i)+1 := by omega
    rw [heq]
    simp only [cbsRun, step, NNReal.coe_sub_def, NNReal.coe_add]
    exact le_rfl
  · intro i hi
    simpa only [hR] using
      (show (arrival c (cbsRun c S R ω (t-c.L+i)) : ℝ) ≤ (R : ℝ) by
        exact_mod_cast cbsRun_arrival_le c S R ω (t-c.L+i))
  · have hb := cbsRun_block_resources c S R ω (t-c.L)
    have hb' : ((cbsRun c S R ω (t-c.L)).1 : ℝ) +
        ∑ i ∈ Finset.range (c.L+1),
          (arrival c (cbsRun c S R ω (t-c.L+i)) : ℝ) ≤ (S : ℝ) := by
      exact_mod_cast hb
    simpa only [Nat.add_zero, hS, Nat.cast_add, Nat.cast_one] using hb'
  · intro i hi
    change ω.1 (reversePrefixIndex t i) = ω.1 (t-c.L+(c.L+1-1-i))
    apply congrArg ω.1
    unfold reversePrefixIndex
    rw [if_pos (by omega)]
    omega

end CappedBaseStockBounds


noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators
open CappedBaseStock

namespace CappedBaseStockBounds

lemma integrable_demand (P : DemandLaw) (i : ℕ) :
    Integrable (fun d : DemandPath => (d i : ℝ)) (demandPathLaw P) := by
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => P.law) i).integrable_comp_of_integrable
    P.finiteMean

lemma integral_demand (P : DemandLaw) (i : ℕ) :
    (∫ d : DemandPath, (d i : ℝ) ∂demandPathLaw P) = mean P := by
  have hm := measurePreserving_eval_infinitePi (fun _ : ℕ => P.law) i
  change (∫ d : DemandPath, ((Function.eval i) d : ℝ) ∂demandPathLaw P) = _
  rw [← integral_map_of_stronglyMeasurable hm.measurable NNReal.continuous_coe.stronglyMeasurable]
  change (∫ x : ℝ≥0, (x : ℝ) ∂(Measure.infinitePi (fun _ : ℕ => P.law)).map
    (Function.eval i)) = mean P
  rw [hm.map_eq]
  rfl

lemma integrable_demand_sum (P : DemandLaw) (r : ℝ) (m : ℕ) :
    Integrable (fun d : DemandPath => ∑ i ∈ Finset.range m, ((d i : ℝ) - r))
      (demandPathLaw P) := by
  exact integrable_finsetSum _ (fun i _ => (integrable_demand P i).sub (integrable_const r))

lemma integral_demand_sum (P : DemandLaw) (r : ℝ) (m : ℕ) :
    (∫ d : DemandPath, (∑ i ∈ Finset.range m, ((d i : ℝ) - r)) ∂demandPathLaw P) =
      (m : ℝ) * (mean P - r) := by
  rw [integral_finsetSum (f := fun i (d : DemandPath) => (d i : ℝ) - r) _
    (fun i _ => (integrable_demand P i).sub (integrable_const r))]
  simp only [integral_sub (f := fun d : DemandPath => (d _ : ℝ)) (g := fun _ => r)
    (integrable_demand P _) (integrable_const r), integral_demand,
    integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]

lemma finiteInventory_succ (d : DemandPath) (r : ℝ) (m : ℕ) :
    finiteInventory d r (m + 1) =
      max (∑ i ∈ Finset.range (m + 1), (r - (d i : ℝ))) (finiteInventory d r m) := by
  unfold finiteInventory
  simp only [Finset.range_add_one (n := m + 1)]
  exact Finset.sup'_insert (by simp) _

lemma finiteInventory_nonneg (d : DemandPath) (r : ℝ) (m : ℕ) :
    0 ≤ finiteInventory d r m := by
  unfold finiteInventory
  simpa only [Finset.range_zero, Finset.sum_empty] using
    Finset.le_sup' (f := fun k => ∑ i ∈ Finset.range k, (r - (d i : ℝ)))
    (by simp : 0 ∈ Finset.range (m + 1))

lemma measurable_finiteInventory (r : ℝ) (m : ℕ) :
    Measurable (fun d : DemandPath => finiteInventory d r m) := by
  induction m with
  | zero => simpa [finiteInventory] using (measurable_const : Measurable (fun _ : DemandPath => (0 : ℝ)))
  | succ m ih =>
    simp only [finiteInventory_succ]
    exact Measurable.max (by fun_prop) ih

lemma integrable_finiteInventory (P : DemandLaw) (r : ℝ) (m : ℕ) :
    Integrable (fun d : DemandPath => finiteInventory d r m) (demandPathLaw P) := by
  induction m with
  | zero => simpa [finiteInventory] using (integrable_const (0 : ℝ) :
      Integrable (fun _ : DemandPath => (0 : ℝ)) (demandPathLaw P))
  | succ m ih =>
    simp only [finiteInventory_succ]
    exact (integrable_finsetSum _ (fun i _ => (integrable_const r).sub
      (integrable_demand P i))).sup ih

lemma inventory_envelope_expectation (P : DemandLaw) (r z : ℝ) (m : ℕ)
    (hrmu : r ≤ mean P) (_hz : 0 ≤ z)
    (hcert : (∫⁻ d, certificateExcess d r z m ∂demandPathLaw P) ≤
      ENNReal.ofReal ((m : ℝ) * (mean P - r))) :
    (∫⁻ d, ENNReal.ofReal (max (finiteInventory d r m)
      (z - ∑ i ∈ Finset.range m, ((d i : ℝ) - r))) ∂demandPathLaw P) ≤
      ENNReal.ofReal z := by
  let B : DemandPath → ℝ := fun d => ∑ i ∈ Finset.range m, ((d i : ℝ) - r)
  let E : DemandPath → ℝ := fun d => max (finiteInventory d r m + B d - z) 0
  have hB : Integrable B (demandPathLaw P) := integrable_demand_sum P r m
  have hE : Integrable E (demandPathLaw P) :=
    (((integrable_finiteInventory P r m).add hB).sub (integrable_const z)).sup
      (integrable_const 0)
  have hEnonneg : 0 ≤ᵐ[demandPathLaw P] E :=
    Filter.Eventually.of_forall (fun d => le_max_right _ _)
  have hEcert : ENNReal.ofReal (∫ d, E d ∂demandPathLaw P) ≤
      ENNReal.ofReal ((m : ℝ) * (mean P - r)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hE hEnonneg]
    simpa [E, B, certificateExcess, ENNReal.ofReal_max] using hcert
  have hEbound : (∫ d, E d ∂demandPathLaw P) ≤ (m : ℝ) * (mean P - r) :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hrmu))).mp hEcert
  have hid (d : DemandPath) : max (finiteInventory d r m) (z - B d) = z - B d + E d := by
    dsimp [E]
    rcases le_total (finiteInventory d r m) (z - B d) with h | h
    · rw [max_eq_right h, max_eq_right (by linarith)]
      ring
    · rw [max_eq_left h, max_eq_left (by linarith)]
      ring
  have hEnv : Integrable (fun d => max (finiteInventory d r m) (z - B d))
      (demandPathLaw P) :=
    (integrable_finiteInventory P r m).sup ((integrable_const z).sub hB)
  rw [← ofReal_integral_eq_lintegral_ofReal hEnv
    (Filter.Eventually.of_forall (fun d => (finiteInventory_nonneg d r m).trans (le_max_left _ _)))]
  apply ENNReal.ofReal_le_ofReal
  simp_rw [hid]
  rw [integral_add (f := fun d => z - B d) (g := E) ((integrable_const z).sub hB) hE,
    integral_sub (f := fun _ => z) (g := B) (integrable_const z) hB]
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  have hBmean : (∫ d, B d ∂demandPathLaw P) = (m : ℝ) * (mean P - r) :=
    integral_demand_sum P r m
  rw [hBmean]
  linarith

lemma excess_envelope_expectation (P : DemandLaw) (r z : ℝ) (m : ℕ)
    (hrmu : r ≤ mean P) (hz : 0 ≤ z)
    (hcert : (∫⁻ d, certificateExcess d r z m ∂demandPathLaw P) ≤
      ENNReal.ofReal ((m : ℝ) * (mean P - r))) :
    (∫⁻ d, ENNReal.ofReal (z + max (finiteInventory d r m +
      (∑ i ∈ Finset.range m, ((d i : ℝ) - r)) - z) 0) ∂demandPathLaw P) ≤
      ENNReal.ofReal (z + (m : ℝ) * (mean P - r)) := by
  have hmax (x : ℝ) : ENNReal.ofReal (max x 0) = ENNReal.ofReal x := by simp
  simp_rw [ENNReal.ofReal_add hz (le_max_right _ _), hmax]
  rw [lintegral_add_left measurable_const]
  simp only [lintegral_const, measure_univ, mul_one]
  rw [ENNReal.ofReal_add hz (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hrmu))]
  exact add_le_add le_rfl hcert

end CappedBaseStockBounds


open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators Topology
noncomputable section
namespace CappedBaseStockBounds
open CappedBaseStock

lemma averageCost_le_of_sum_bound (P : DemandLaw) (f : ℕ → Sample → ℝ≥0∞)
    (a C : ℝ≥0∞) (hC : C ≠ ∞)
    (h : ∀ᶠ T : ℕ in atTop,
      (∑ t ∈ Finset.range (T+1), ∫⁻ ω, f t ω ∂sampleLaw P) ≤ a*(T+1)+C) :
    averageCost P f ≤ a := by
  have hlim : Tendsto (fun T : ℕ => a + C / (T+1 : ℝ≥0∞)) atTop (𝓝 a) := by
    have hinv : Tendsto (fun T : ℕ => ((T+1 : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 0) :=
      ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    have hmul := ENNReal.Tendsto.const_mul hinv (Or.inr hC)
    simpa [div_eq_mul_inv] using tendsto_const_nhds.add hmul
  unfold averageCost
  apply (limsup_le_limsup ?_).trans (le_of_eq hlim.limsup_eq)
  filter_upwards [h] with T hT
  calc
    _ ≤ (a * (T+1) + C) / (T+1) := ENNReal.div_le_div_right hT _
    _ = a + C / (T+1) := by
      rw [ENNReal.add_div, ENNReal.mul_div_cancel_right (by simp) (by simp)]

lemma averageCost_le_of_lintegral_le (P : DemandLaw) (f : ℕ → Sample → ℝ≥0∞)
    (a : ℝ≥0∞) (h : ∀ t, (∫⁻ ω, f t ω ∂sampleLaw P) ≤ a) :
    averageCost P f ≤ a := by
  apply averageCost_le_of_sum_bound P f a 0 (by simp)
  apply Filter.Eventually.of_forall
  intro T
  calc
    _ ≤ ∑ t ∈ Finset.range (T+1), a := Finset.sum_le_sum (fun t _ => h t)
    _ = _ := by simp [mul_comm]

lemma sum_le_of_eventually_le (u : ℕ → ℝ≥0∞) (a B : ℝ≥0∞) (m : ℕ)
    (hB : ∀ t, u t ≤ B) (ha : ∀ t, m ≤ t → u t ≤ a) (N : ℕ) :
    (∑ t ∈ Finset.range N, u t) ≤ a*N+B*m := by
  by_cases hm : m ≤ N
  · rw [← Finset.sum_range_add_sum_Ico u hm]
    have hb : (∑ t ∈ Finset.range m, u t) ≤ B*m := by
      calc
        _ ≤ ∑ t ∈ Finset.range m, B := Finset.sum_le_sum (fun t _ => hB t)
        _ = _ := by simp [mul_comm]
    have ht : (∑ t ∈ Finset.Ico m N, u t) ≤ a*N := by
      calc
        _ ≤ ∑ t ∈ Finset.Ico m N, a := Finset.sum_le_sum (fun t ht => ha t (Finset.mem_Ico.mp ht).1)
        _ = a*(N-m : ℕ) := by simp [mul_comm]
        _ ≤ a*N := by gcongr; omega
    simpa [add_comm] using add_le_add hb ht
  · have hnm : N ≤ m := by omega
    calc
      _ ≤ ∑ t ∈ Finset.range N, B := Finset.sum_le_sum (fun t _ => hB t)
      _ = B*N := by simp [mul_comm]
      _ ≤ B*m := by gcongr
      _ ≤ a*N+B*m := le_add_left le_rfl

lemma averageCost_le_of_eventually_lintegral_le (P : DemandLaw)
    (f : ℕ → Sample → ℝ≥0∞) (a B : ℝ≥0∞) (hBtop : B ≠ ∞)
    (hB : ∀ t, (∫⁻ ω, f t ω ∂sampleLaw P) ≤ B)
    (h : ∀ᶠ t : ℕ in atTop, (∫⁻ ω, f t ω ∂sampleLaw P) ≤ a) :
    averageCost P f ≤ a := by
  obtain ⟨m, hm⟩ := Filter.eventually_atTop.mp h
  apply averageCost_le_of_sum_bound P f a (B*m) (ENNReal.mul_ne_top hBtop (by simp))
  apply Filter.Eventually.of_forall
  intro T
  simpa only [Nat.cast_add, Nat.cast_one] using
    sum_le_of_eventually_le _ a B m hB hm (T+1)

end CappedBaseStockBounds


noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open CappedBaseStock
namespace CappedBaseStockBounds

lemma integrable_cbs_inventory (P : DemandLaw) (c : Parameters) (S r : ℝ≥0) (t : ℕ) :
    Integrable (fun ω => ((cbsRun c S r ω t).1 : ℝ)) (sampleLaw P) := by
  apply (integrable_const (S : ℝ)).mono'
  · have hm := (measurable_cbsRun c S r t).fst
    exact (NNReal.continuous_coe.measurable.comp hm).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro ω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)] using
      (show ((cbsRun c S r ω t).1 : ℝ) ≤ (S : ℝ) from
        NNReal.coe_le_coe.mpr (cbsRun_inventory_le c S r ω t))

lemma integral_inventory_le_of_lintegral (P : DemandLaw) (c : Parameters)
    (S r : ℝ≥0) (t : ℕ) (z : ℝ) (hz : 0 ≤ z)
    (h : (∫⁻ ω, ((cbsRun c S r ω t).1 : ℝ≥0∞) ∂sampleLaw P) ≤ ENNReal.ofReal z) :
    (∫ ω, ((cbsRun c S r ω t).1 : ℝ) ∂sampleLaw P) ≤ z := by
  apply (ENNReal.ofReal_le_ofReal_iff hz).mp
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_cbs_inventory P c S r t)
    (Filter.Eventually.of_forall (fun _ => NNReal.coe_nonneg _))]
  simpa only [ENNReal.ofReal_coe_nnreal] using h

lemma finite_cap_inventory_lintegral (P : DemandLaw) (c : Parameters) (r z : ℝ)
    (feasible : CertificateFeasible P c r z) (t : ℕ) :
    (∫⁻ ω, ((cbsRun c (Real.toNNReal (((c.L : ℝ)+1)*r+z))
      (Real.toNNReal r) ω (t+1)).1 : ℝ≥0∞) ∂sampleLaw P) ≤ ENNReal.ofReal z := by
  by_cases ht : c.L ≤ t
  · let F : DemandPath → ℝ≥0∞ := fun d =>
      ENNReal.ofReal (max (finiteInventory d r (c.L+1))
        (z - ∑ i ∈ Finset.range (c.L+1), ((d i : ℝ)-r)))
    have hF : Measurable F := by
      have hm := measurable_finiteInventory r (c.L+1)
      dsimp [F]
      fun_prop
    calc
      _ ≤ ∫⁻ ω, F (fun i => ω.1 (reversePrefixIndex t i)) ∂sampleLaw P := by
        apply lintegral_mono
        intro ω
        dsimp only
        rw [← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal
          (cbsRun_inventory_envelope c r z feasible.1 feasible.2.2.1 ω t ht)
      _ = ∫⁻ d, F d ∂demandPathLaw P :=
        lintegral_sample_reindex P (reversePrefixIndex t)
          (reversePrefixIndex_injective t) F hF
      _ ≤ ENNReal.ofReal z := inventory_envelope_expectation P r z (c.L+1)
        feasible.2.1 feasible.2.2.1 (by
          simpa only [Nat.cast_add, Nat.cast_one] using feasible.2.2.2.2)
  · have hz (ω : Sample) : (cbsRun c (Real.toNNReal (((c.L : ℝ)+1)*r+z))
        (Real.toNNReal r) ω (t+1)).1 = 0 :=
      cbsRun_inventory_zero_initial c _ _ ω (t+1) (by omega)
    simp only [hz, ENNReal.coe_zero, lintegral_zero]
    exact zero_le

lemma finite_cap_inventory_proved (P : DemandLaw) (c : Parameters) (r z : ℝ)
    (feasible : CertificateFeasible P c r z) :
    averageCost P (fun t ω =>
      ((cbsRun c (Real.toNNReal (((c.L : ℝ) + 1) * r + z))
        (Real.toNNReal r) ω (t + 1)).1 : ℝ≥0∞)) ≤ ENNReal.ofReal z := by
  exact averageCost_le_of_lintegral_le P _ (ENNReal.ofReal z)
    (finite_cap_inventory_lintegral P c r z feasible)

end CappedBaseStockBounds

open CappedBaseStock


theorem solution (P : DemandLaw) (c : Parameters) (r z : ℝ)
    (feasible : CertificateFeasible P c r z) :
    averageCost P (fun t ω =>
      ((cbsRun c (Real.toNNReal (((c.L : ℝ) + 1) * r + z))
        (Real.toNNReal r) ω (t + 1)).1 : ℝ≥0∞)) ≤ ENNReal.ofReal z := by
  exact CappedBaseStockBounds.finite_cap_inventory_proved P c r z feasible

