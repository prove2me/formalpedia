-- Prove2me | solution 1 for CappedBaseStock.base_stock_average_loss_scan
-- status  : ACCEPTED   (prove)
-- author  : @StellaXin
-- created : 2026-09-08T02:46:03.035729+00:00
-- url     : https://prove2.me/submissions/cc62e691-39d9-45c4-90c2-a39b1eae8e67

import Definitions.Def_CappedBaseStock_BaseStockAnalysis
import Definitions.Def_CappedBaseStock_Model

-- Proven component: Definitions/Def_CappedBaseStock_Integration.lean
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators
namespace CBSBaseStockIntegration
open CappedBaseStock

lemma demand_measurePreserving (P : DemandLaw) (t : ℕ) :
    MeasurePreserving (fun ω : Sample => ω.1 t) (sampleLaw P) P.law := by
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => P.law) t).comp
    (measurePreserving_fst (μ := demandPathLaw P) (ν := seedLaw))

lemma demand_integrable (P : DemandLaw) (t : ℕ) :
    Integrable (fun ω : Sample => (ω.1 t : ℝ)) (sampleLaw P) := by
  exact (demand_measurePreserving P t).integrable_comp_of_integrable P.finiteMean

lemma demand_integral (P : DemandLaw) (t : ℕ) :
    (∫ ω : Sample, (ω.1 t : ℝ) ∂sampleLaw P) = mean P := by
  have hd := demand_measurePreserving P t
  rw [mean, ← hd.map_eq]
  exact (integral_map hd.aemeasurable (by fun_prop)).symm

lemma loss_measurable (c : Parameters) (S r : ℝ≥0) (t : ℕ) :
    Measurable (fun ω : Sample =>
      (lostSales c (cbsRun c S r ω t) (ω.1 t) : ℝ)) := by
  have hs := measurable_cbsRun c S r t
  unfold lostSales arrival
  fun_prop

lemma loss_integrable (P : DemandLaw) (c : Parameters) (S r : ℝ≥0) (t : ℕ) :
    Integrable (fun ω : Sample =>
      (lostSales c (cbsRun c S r ω t) (ω.1 t) : ℝ)) (sampleLaw P) := by
  refine (demand_integrable P t).mono' (loss_measurable c S r t).aestronglyMeasurable ?_
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
  exact_mod_cast (tsub_le_self : ω.1 t - ((cbsRun c S r ω t).1 + arrival c (cbsRun c S r ω t)) ≤ ω.1 t)

lemma loss_integral_nonneg (P : DemandLaw) (c : Parameters) (S r : ℝ≥0) (t : ℕ) :
    0 ≤ ∫ ω : Sample, (lostSales c (cbsRun c S r ω t) (ω.1 t) : ℝ) ∂sampleLaw P := by
  exact integral_nonneg (fun _ => NNReal.coe_nonneg _)

lemma loss_integral_le_mean (P : DemandLaw) (c : Parameters) (S r : ℝ≥0) (t : ℕ) :
    (∫ ω : Sample, (lostSales c (cbsRun c S r ω t) (ω.1 t) : ℝ) ∂sampleLaw P) ≤ mean P := by
  rw [← demand_integral P t]
  apply integral_mono (loss_integrable P c S r t) (demand_integrable P t)
  intro ω
  exact_mod_cast (tsub_le_self : ω.1 t - ((cbsRun c S r ω t).1 + arrival c (cbsRun c S r ω t)) ≤ ω.1 t)

lemma lintegral_loss_eq (P : DemandLaw) (c : Parameters) (S r : ℝ≥0) (t : ℕ) :
    (∫⁻ ω : Sample, (lostSales c (cbsRun c S r ω t) (ω.1 t) : ℝ≥0∞) ∂sampleLaw P) =
      ENNReal.ofReal (∫ ω : Sample, (lostSales c (cbsRun c S r ω t) (ω.1 t) : ℝ) ∂sampleLaw P) := by
  exact lintegral_coe_eq_integral _ (loss_integrable P c S r t)

end CBSBaseStockIntegration

-- Proven component: Solutions/CbsBaseStockDynamics.lean
noncomputable section
open scoped NNReal ENNReal BigOperators

namespace CappedBaseStock

def bsPos {L : ℕ} (s : State L) : ℝ :=
  (s.1 : ℝ) + ∑ i : Fin L, (s.2 i : ℝ)

def bsWeight {L : ℕ} (s : State L) : ℝ :=
  ∑ i : Fin L, ((i.val : ℝ) + 1) * (s.2 i : ℝ)

lemma bs_queue_sum (L : ℕ) (hL : 0 < L) (x : Fin L → ℝ≥0) (q : ℝ≥0) :
    (∑ i : Fin L, (if hi : i.val + 1 < L then (x ⟨i.val + 1, hi⟩ : ℝ) else (q : ℝ))) +
      (x ⟨0, hL⟩ : ℝ) = (∑ i : Fin L, (x i : ℝ)) + (q : ℝ) := by
  cases L with
  | zero => omega
  | succ n =>
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
    simp only [Fin.val_last, lt_self_iff_false, dite_false]
    have heq : (∑ i : Fin n, if hi : i.castSucc.val + 1 < n + 1 then
        (x ⟨i.castSucc.val + 1, hi⟩ : ℝ) else (q : ℝ)) =
        ∑ i : Fin n, (x i.succ : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Fin.val_castSucc, Nat.succ_lt_succ_iff, i.isLt, dite_true]
      rfl
    rw [heq]
    have hz : (⟨0, hL⟩ : Fin (n + 1)) = 0 := rfl
    rw [hz]
    ring

lemma bs_queue_weight (L : ℕ) (hL : 0 < L) (x : Fin L → ℝ≥0) (q : ℝ≥0) :
    (∑ i : Fin L, ((i.val : ℝ) + 1) *
      (if hi : i.val + 1 < L then (x ⟨i.val + 1, hi⟩ : ℝ) else (q : ℝ))) +
      (∑ i : Fin L, (x i : ℝ)) =
      (∑ i : Fin L, ((i.val : ℝ) + 1) * (x i : ℝ)) + (L : ℝ) * (q : ℝ) := by
  cases L with
  | zero => omega
  | succ n =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_last, lt_self_iff_false, dite_false]
    have heq : (∑ i : Fin n, ((i.castSucc.val : ℝ) + 1) *
        (if hi : i.castSucc.val + 1 < n + 1 then
          (x ⟨i.castSucc.val + 1, hi⟩ : ℝ) else (q : ℝ))) =
        ∑ i : Fin n, ((i.val : ℝ) + 1) * (x i.succ : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Fin.val_castSucc, Nat.succ_lt_succ_iff, i.isLt, dite_true]
      rfl
    rw [heq, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.cast_zero, zero_add, one_mul, Fin.val_succ, Nat.cast_add,
      Nat.cast_one]
    have hs : (∑ i : Fin n, ((i.val : ℝ) + 1 + 1) * (x i.succ : ℝ)) =
        (∑ i : Fin n, ((i.val : ℝ) + 1) * (x i.succ : ℝ)) +
        ∑ i : Fin n, (x i.succ : ℝ) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hs]
    ring

lemma bs_pos_nonneg {L : ℕ} (s : State L) : 0 ≤ bsPos s := by
  unfold bsPos
  positivity

lemma bs_available_le_pos (c : Parameters) (s : State c.L) :
    ((s.1 + arrival c s : ℝ≥0) : ℝ) ≤ bsPos s := by
  simp only [NNReal.coe_add, bsPos]
  apply add_le_add le_rfl
  exact Finset.single_le_sum (fun i _ => (s.2 i).coe_nonneg) (Finset.mem_univ _)

lemma bs_fill_le_pos (c : Parameters) (s : State c.L) (d : ℝ≥0) :
    (filledDemand c s d : ℝ) ≤ bsPos s := by
  calc
    _ ≤ ((s.1 + arrival c s : ℝ≥0) : ℝ) := by
      exact_mod_cast min_le_right d (s.1 + arrival c s)
    _ ≤ _ := bs_available_le_pos c s

lemma bs_step_inventory (c : Parameters) (s : State c.L) (q d : ℝ≥0) :
    ((step c s q d).1 : ℝ) + (filledDemand c s d : ℝ) =
      (s.1 : ℝ) + (arrival c s : ℝ) := by
  simp only [step, filledDemand, NNReal.coe_add, NNReal.coe_sub_def, NNReal.coe_min]
  rcases le_total (d : ℝ) ((s.1 : ℝ) + (arrival c s : ℝ)) with h | h
  · rw [min_eq_left h, max_eq_left (sub_nonneg.mpr h)]
    ring
  · rw [min_eq_right h, max_eq_right (sub_nonpos.mpr h)]
    ring

lemma bs_step_pos (c : Parameters) (s : State c.L) (q d : ℝ≥0) :
    bsPos (step c s q d) + (filledDemand c s d : ℝ) = bsPos s + (q : ℝ) := by
  have hq := bs_queue_sum c.L (lt_of_lt_of_le Nat.zero_lt_one c.leadTime_pos) s.2 q
  have hi := bs_step_inventory c s q d
  have heq : (∑ i : Fin c.L, ((if hi : i.val + 1 < c.L then s.2 ⟨i.val + 1, hi⟩ else q : ℝ≥0) : ℝ)) =
      ∑ i : Fin c.L, if hi : i.val + 1 < c.L then (s.2 ⟨i.val + 1, hi⟩ : ℝ) else (q : ℝ) := by
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> rfl
  unfold bsPos
  change ((step c s q d).1 : ℝ) +
    (∑ i : Fin c.L, ((if hi : i.val + 1 < c.L then s.2 ⟨i.val + 1, hi⟩ else q : ℝ≥0) : ℝ)) +
      (filledDemand c s d : ℝ) = _
  rw [heq]
  change _ + (s.2 ⟨0, _⟩ : ℝ) = _ at hq
  unfold arrival at hi
  linarith

lemma bs_order_eq (c : Parameters) (S : ℝ≥0) (s : State c.L)
    (hs : bsPos s ≤ (S : ℝ)) :
    (cbsOrder c.L S S s : ℝ) = (S : ℝ) - bsPos s := by
  unfold cbsOrder
  rw [min_eq_left (tsub_le_self : S - (s.1 + ∑ i, s.2 i) ≤ S)]
  rw [NNReal.coe_sub]
  · simp [bsPos]
  · apply NNReal.coe_le_coe.mp
    simpa only [bsPos, NNReal.coe_add, NNReal.coe_sum] using hs

lemma bs_pos_bound (c : Parameters) (S : ℝ≥0) (ω : Sample) (t : ℕ) :
    bsPos (cbsRun c S S ω t) ≤ (S : ℝ) := by
  induction t with
  | zero => simp [cbsRun, initialState, bsPos]
  | succ t ih =>
    have hp := bs_step_pos c (cbsRun c S S ω t)
      (cbsOrder c.L S S (cbsRun c S S ω t)) (ω.1 t)
    rw [bs_order_eq c S _ ih] at hp
    change bsPos (cbsRun c S S ω (t+1)) + _ = _ at hp
    linarith [(filledDemand c (cbsRun c S S ω t) (ω.1 t)).coe_nonneg]

lemma bs_pos_fill (c : Parameters) (S : ℝ≥0) (ω : Sample) (t : ℕ) :
    bsPos (cbsRun c S S ω (t+1)) +
      (filledDemand c (cbsRun c S S ω t) (ω.1 t) : ℝ) = (S : ℝ) := by
  have hp := bs_step_pos c (cbsRun c S S ω t)
    (cbsOrder c.L S S (cbsRun c S S ω t)) (ω.1 t)
  rw [bs_order_eq c S _ (bs_pos_bound c S ω t)] at hp
  change bsPos (cbsRun c S S ω (t+1)) + _ = _ at hp
  linarith

lemma bs_inventory_le (c : Parameters) (S : ℝ≥0) (ω : Sample) (t : ℕ) :
    ((cbsRun c S S ω t).1 : ℝ) ≤ (S : ℝ) := by
  have h := bs_pos_bound c S ω t
  have hp : 0 ≤ ∑ i : Fin c.L, ((cbsRun c S S ω t).2 i : ℝ) := by positivity
  unfold bsPos at h
  linarith

lemma bs_order_initial (c : Parameters) (S : ℝ≥0) (ω : Sample) :
    cbsOrder c.L S S (cbsRun c S S ω 0) = S := by
  simp [cbsRun, initialState, cbsOrder]

lemma bs_order_next (c : Parameters) (S : ℝ≥0) (ω : Sample) (t : ℕ) :
    (cbsOrder c.L S S (cbsRun c S S ω (t+1)) : ℝ) =
      (filledDemand c (cbsRun c S S ω t) (ω.1 t) : ℝ) := by
  rw [bs_order_eq c S _ (bs_pos_bound c S ω (t+1))]
  linarith [bs_pos_fill c S ω t]

lemma bs_step_weight (c : Parameters) (s : State c.L) (q d : ℝ≥0) :
    bsWeight (step c s q d) + (∑ i : Fin c.L, (s.2 i : ℝ)) =
      bsWeight s + (c.L : ℝ) * (q : ℝ) := by
  have heq : (∑ i : Fin c.L, ((i.val : ℝ) + 1) *
      ((if hi : i.val + 1 < c.L then s.2 ⟨i.val + 1, hi⟩ else q : ℝ≥0) : ℝ)) =
      ∑ i : Fin c.L, ((i.val : ℝ) + 1) *
        (if hi : i.val + 1 < c.L then (s.2 ⟨i.val + 1, hi⟩ : ℝ) else (q : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> rfl
  unfold bsWeight step
  rw [heq]
  exact bs_queue_weight c.L (lt_of_lt_of_le Nat.zero_lt_one c.leadTime_pos) s.2 q

lemma bs_weight_bound (c : Parameters) (S : ℝ≥0) (s : State c.L)
    (hs : bsPos s ≤ (S : ℝ)) : bsWeight s ≤ (c.L : ℝ) * (S : ℝ) := by
  have hp : (∑ i : Fin c.L, (s.2 i : ℝ)) ≤ (S : ℝ) := by
    unfold bsPos at hs
    linarith [s.1.coe_nonneg]
  calc
    bsWeight s ≤ (c.L : ℝ) * ∑ i : Fin c.L, (s.2 i : ℝ) := by
      unfold bsWeight
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right _ (s.2 i).coe_nonneg
      exact_mod_cast (show i.val + 1 ≤ c.L by omega)
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg c.L)

lemma bs_weight_one (c : Parameters) (S : ℝ≥0) (ω : Sample) :
    bsWeight (cbsRun c S S ω 1) = (c.L : ℝ) * (S : ℝ) := by
  have hw := bs_step_weight c (cbsRun c S S ω 0)
    (cbsOrder c.L S S (cbsRun c S S ω 0)) (ω.1 0)
  rw [bs_order_initial] at hw
  change bsWeight (step c (cbsRun c S S ω 0) S (ω.1 0)) + _ = _ at hw
  simpa [cbsRun, initialState, bsWeight, cbsOrder] using hw

lemma bs_one_period_accounting (c : Parameters) (S : ℝ≥0) (ω : Sample) (t : ℕ) :
    ((cbsRun c S S ω (t+1)).1 : ℝ) +
      ((c.L : ℝ) + 1) * (filledDemand c (cbsRun c S S ω t) (ω.1 t) : ℝ) =
      (S : ℝ) + bsWeight (cbsRun c S S ω (t+2)) - bsWeight (cbsRun c S S ω (t+1)) := by
  have hp := bs_pos_fill c S ω t
  have hw := bs_step_weight c (cbsRun c S S ω (t+1))
    (cbsOrder c.L S S (cbsRun c S S ω (t+1))) (ω.1 (t+1))
  rw [bs_order_next] at hw
  change bsWeight (cbsRun c S S ω (t+2)) + _ = _ at hw
  unfold bsPos at hp
  nlinarith

lemma bs_total_inventory_identity (c : Parameters) (S : ℝ≥0) (ω : Sample) (N : ℕ) :
    (∑ t ∈ Finset.range N, ((cbsRun c S S ω (t+1)).1 : ℝ)) +
      ((c.L : ℝ) + 1) *
        (∑ t ∈ Finset.range N, (filledDemand c (cbsRun c S S ω t) (ω.1 t) : ℝ)) =
      (N : ℝ) * (S : ℝ) + bsWeight (cbsRun c S S ω (N+1)) - (c.L : ℝ) * (S : ℝ) := by
  induction N with
  | zero => simp [bs_weight_one]
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have ht := bs_one_period_accounting c S ω N
    push_cast
    nlinarith

lemma bs_total_inventory_bound (c : Parameters) (S : ℝ≥0) (ω : Sample) (N : ℕ) :
    (∑ t ∈ Finset.range N, ((cbsRun c S S ω (t+1)).1 : ℝ)) ≤
      (N : ℝ) * (S : ℝ) - ((c.L : ℝ) + 1) *
        (∑ t ∈ Finset.range N, (filledDemand c (cbsRun c S S ω t) (ω.1 t) : ℝ)) := by
  have hi := bs_total_inventory_identity c S ω N
  have hw := bs_weight_bound c S (cbsRun c S S ω (N+1)) (bs_pos_bound c S ω (N+1))
  linarith

end CappedBaseStock

-- Proven component: Solutions/CbsBaseStockLossDynamics.lean
noncomputable section
open scoped NNReal ENNReal BigOperators

namespace CappedBaseStock

lemma bs_order_fill (c : Parameters) (S : ℝ≥0) (ω : Sample) (t : ℕ) :
    (cbsOrder c.L S S (cbsRun c S S ω (t + 1)) : ℝ) =
      (filledDemand c (cbsRun c S S ω t) (ω.1 t) : ℝ) := by
  rw [bs_order_eq c S _ (bs_pos_bound c S ω (t + 1))]
  linarith [bs_pos_fill c S ω t]

private lemma bs_queue_age (c : Parameters) (S : ℝ≥0) (ω : Sample) (t k : ℕ)
    (i : Fin c.L) (hi : i.val + k + 1 = c.L) :
    (cbsRun c S S ω (t + k + 1)).2 i = cbsOrder c.L S S (cbsRun c S S ω t) := by
  induction k generalizing i with
  | zero =>
    simp only [Nat.add_zero, cbsRun, step]
    rw [dif_neg (by omega)]
  | succ k ih =>
    have hi' : i.val + 1 < c.L := by omega
    have ht : t + (k + 1) + 1 = (t + k + 1) + 1 := by omega
    rw [ht, cbsRun]
    dsimp only [step]
    rw [dif_pos hi']
    exact ih ⟨i.val + 1, hi'⟩ (by dsimp; omega)

lemma bs_pipeline_order (c : Parameters) (S : ℝ≥0) (ω : Sample) (t : ℕ) (i : Fin c.L) :
    (cbsRun c S S ω (t + c.L)).2 i =
      cbsOrder c.L S S (cbsRun c S S ω (t + i.val)) := by
  have h := bs_queue_age c S ω (t + i.val) (c.L - i.val - 1) i (by omega)
  have ht : t + i.val + (c.L - i.val - 1) + 1 = t + c.L := by omega
  rwa [ht] at h

lemma bs_pipeline_fill (c : Parameters) (S : ℝ≥0) (ω : Sample) (t : ℕ) (i : Fin c.L) :
    ((cbsRun c S S ω (t + c.L + 1)).2 i : ℝ) =
      (filledDemand c (cbsRun c S S ω (t + i.val)) (ω.1 (t + i.val)) : ℝ) := by
  rw [show t + c.L + 1 = (t + 1) + c.L by omega, bs_pipeline_order]
  rw [show t + 1 + i.val = (t + i.val) + 1 by omega, bs_order_fill]

lemma bs_available_window (c : Parameters) (S : ℝ≥0) (ω : Sample) (t : ℕ) :
    ((cbsRun c S S ω (t + c.L)).1 : ℝ) +
      (arrival c (cbsRun c S S ω (t + c.L)) : ℝ) +
      (∑ i ∈ Finset.range c.L,
        (filledDemand c (cbsRun c S S ω (t + i)) (ω.1 (t + i)) : ℝ)) = (S : ℝ) := by
  have hp := bs_pos_fill c S ω (t + c.L)
  have hi := bs_step_inventory c (cbsRun c S S ω (t + c.L))
    (cbsOrder c.L S S (cbsRun c S S ω (t + c.L))) (ω.1 (t + c.L))
  change ((cbsRun c S S ω (t + c.L + 1)).1 : ℝ) + _ = _ at hi
  unfold bsPos at hp
  have hq : (∑ i : Fin c.L, ((cbsRun c S S ω (t + c.L + 1)).2 i : ℝ)) =
      ∑ i ∈ Finset.range c.L,
        (filledDemand c (cbsRun c S S ω (t + i)) (ω.1 (t + i)) : ℝ) := by
    simp_rw [bs_pipeline_fill]
    exact Fin.sum_univ_eq_sum_range
      (fun i => (filledDemand c (cbsRun c S S ω (t + i)) (ω.1 (t + i)) : ℝ)) c.L
  rw [hq] at hp
  linarith

lemma bs_filled_add_lost (c : Parameters) (s : State c.L) (d : ℝ≥0) :
    (filledDemand c s d : ℝ) + (lostSales c s d : ℝ) = (d : ℝ) := by
  have h : lostSales c s d + filledDemand c s d = d := tsub_add_min
  exact_mod_cast (add_comm (filledDemand c s d) (lostSales c s d)).trans h

lemma bs_loss_recursion (c : Parameters) (S : ℝ≥0) (ω : Sample) (t : ℕ) :
    (lostSales c (cbsRun c S S ω (t + c.L)) (ω.1 (t + c.L)) : ℝ) =
      max ((∑ i ∈ Finset.range (c.L + 1), (ω.1 (t + i) : ℝ)) - (S : ℝ) -
        ∑ i ∈ Finset.range c.L,
          (lostSales c (cbsRun c S S ω (t + i)) (ω.1 (t + i)) : ℝ)) 0 := by
  have ha := bs_available_window c S ω t
  have hsum : (∑ i ∈ Finset.range c.L,
        (filledDemand c (cbsRun c S S ω (t + i)) (ω.1 (t + i)) : ℝ)) +
      (∑ i ∈ Finset.range c.L,
        (lostSales c (cbsRun c S S ω (t + i)) (ω.1 (t + i)) : ℝ)) =
      ∑ i ∈ Finset.range c.L, (ω.1 (t + i) : ℝ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact bs_filled_add_lost c _ _
  rw [Finset.sum_range_succ]
  conv_lhs => rw [lostSales, NNReal.coe_sub_def, NNReal.coe_add]
  congr 1
  linarith

end CappedBaseStock

-- Proven component: Solutions/Sol_CappedBaseStock_base_stock_average_loss_scan.lean
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators
namespace CBSBaseStockScanProof
open CappedBaseStock CBSBaseStockIntegration

lemma sum_le_of_block_bound (a : ℕ → ℝ) (q L : ℕ) (hq : 0 < q)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ha : ∀ n, a n ≤ D)
    (hb : ∀ m, L ≤ m → ∑ i ∈ Finset.range q, a (m + i) ≤ C) :
    ∀ N, ∑ i ∈ Finset.range N, a i ≤ (N : ℝ) * (C / q) + (L + q : ℕ) * D := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hsmall : N ≤ L + q
    · calc
        ∑ i ∈ Finset.range N, a i ≤ ∑ _i ∈ Finset.range N, D :=
          Finset.sum_le_sum (fun i _ => ha i)
        _ = (N : ℝ) * D := by simp
        _ ≤ (L + q : ℕ) * D := mul_le_mul_of_nonneg_right (by exact_mod_cast hsmall) hD
        _ ≤ _ := le_add_of_nonneg_left (by positivity)
    · have hNq : q ≤ N := by omega
      have hN : N - q + q = N := Nat.sub_add_cancel hNq
      have hi := ih (N - q) (by omega)
      have hb' := hb (N - q) (by omega)
      have hcast : ((N - q : ℕ) : ℝ) + (q : ℝ) = (N : ℝ) := by exact_mod_cast hN
      have hq0 : (q : ℝ) ≠ 0 := by positivity
      have hmul : (q : ℝ) * (C / q) = C := by field_simp
      calc
        ∑ i ∈ Finset.range N, a i =
            (∑ i ∈ Finset.range (N - q), a i) +
              ∑ i ∈ Finset.range q, a (N - q + i) := by
                rw [← Finset.sum_range_add, hN]
        _ ≤ (N - q : ℕ) * (C / q) + (L + q : ℕ) * D + C := add_le_add hi hb'
        _ = (((N - q : ℕ) : ℝ) + q) * (C / q) + (L + q : ℕ) * D := by
          rw [add_mul, hmul]
          ring
        _ = _ := by rw [hcast]

lemma ennreal_average_le_of_block_bound (a : ℕ → ℝ) (q L : ℕ) (hq : 0 < q)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ha0 : ∀ n, 0 ≤ a n) (ha : ∀ n, a n ≤ D)
    (hb : ∀ m, L ≤ m → ∑ i ∈ Finset.range q, a (m + i) ≤ C) :
    Filter.limsup (fun T : ℕ =>
      (∑ t ∈ Finset.range (T + 1), ENNReal.ofReal (a t)) / (T + 1 : ℝ≥0∞)) atTop ≤
      ENNReal.ofReal (C / q) := by
  let bound : ℕ → ℝ := fun T => C / q + ((L + q : ℕ) : ℝ) * D / (T + 1)
  have hle : ∀ T : ℕ,
      (∑ t ∈ Finset.range (T + 1), ENNReal.ofReal (a t)) / (T + 1 : ℝ≥0∞) ≤
        ENNReal.ofReal (bound T) := by
    intro T
    have hsum := sum_le_of_block_bound a q L hq C D hC hD ha hb (T+1)
    have ht : 0 < (T : ℝ) + 1 := by positivity
    have hdiv : (∑ t ∈ Finset.range (T + 1), a t) / ((T : ℝ) + 1) ≤ bound T := by
      apply (div_le_iff₀ ht).mpr
      dsimp [bound]
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt ht)]
      simpa [Nat.cast_add, Nat.cast_one, mul_comm] using hsum
    have hden : ENNReal.ofReal ((T : ℝ) + 1) = (T + 1 : ℝ≥0∞) := by
      simp [ENNReal.ofReal_add (Nat.cast_nonneg T) zero_le_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => ha0 i), ← hden,
      ← ENNReal.ofReal_div_of_pos ht]
    exact ENNReal.ofReal_le_ofReal hdiv
  have ht : Tendsto (fun T : ℕ => (T : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hconv : Tendsto bound atTop (nhds (C / q)) := by
    simpa [bound] using (tendsto_const_nhds.add (tendsto_const_nhds.div_atTop ht) :
      Tendsto (fun T : ℕ => C / q + ((L + q : ℕ) : ℝ) * D / ((T : ℝ) + 1))
        atTop (nhds (C / q + 0)))
  exact (Filter.limsup_le_limsup (Filter.Eventually.of_forall hle)).trans_eq
    (ENNReal.tendsto_ofReal hconv).limsup_eq

lemma scanDemand_measurable (L : ℕ) : Measurable (fun d : DemandPath => scanDemand d L) := by
  unfold scanDemand
  have h := Finset.measurable_sup' (s := Finset.range (L+1)) (by simp)
    (f := fun j (d : DemandPath) => ∑ i ∈ Finset.range (L+1), (d (j+i) : ℝ))
    (by intro j hj; fun_prop)
  convert h using 1
  funext d
  exact (Finset.sup'_apply (by simp : (Finset.range (L+1)).Nonempty)
    (fun j (d : DemandPath) => ∑ i ∈ Finset.range (L+1), (d (j+i) : ℝ)) d).symm

lemma scanExcess_measurable (L : ℕ) (S : ℝ) :
    Measurable (fun d : DemandPath => scanExcess d L S) := by
  exact (scanDemand_measurable L |>.sub measurable_const).ennreal_ofReal

lemma shift_measurePreserving (P : DemandLaw) (m : ℕ) :
    MeasurePreserving (fun d : DemandPath => fun j => d (m+j))
      (demandPathLaw P) (demandPathLaw P) := by
  constructor
  · fun_prop
  · exact Measure.map_infinitePi_infinitePi_of_inj (fun i j hij => Nat.add_left_cancel hij)

lemma lintegral_scan_shift (P : DemandLaw) (L m : ℕ) (S : ℝ) :
    (∫⁻ ω : Sample, scanExcess (fun j => ω.1 (m+j)) L S ∂sampleLaw P) =
      ∫⁻ d, scanExcess d L S ∂demandPathLaw P := by
  have hm := (shift_measurePreserving P m).comp
    (measurePreserving_fst (μ := demandPathLaw P) (ν := seedLaw))
  exact hm.lintegral_comp (scanExcess_measurable L S)

lemma block_from_recursion (L : ℕ) (S : ℝ) (d a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n)
    (hrec : ∀ t, a (t+L) = max
      ((∑ i ∈ Finset.range (L+1), d (t+i)) - S - ∑ i ∈ Finset.range L, a (t+i)) 0)
    (t : ℕ) :
    (∑ i ∈ Finset.range (L+1), a (t+L+i)) ≤
      max ((Finset.range (L+1)).sup' (by simp)
        (fun j => ∑ i ∈ Finset.range (L+1), d (t+j+i)) - S) 0 := by
  classical
  let B := max ((Finset.range (L+1)).sup' (by simp)
    (fun j => ∑ i ∈ Finset.range (L+1), d (t+j+i)) - S) 0
  have hB : 0 ≤ B := le_max_right _ _
  have hwindow : ∀ i < L+1,
      (∑ j ∈ Finset.range (L+1), d (t+i+j)) - S ≤ B := by
    intro i hi
    exact (sub_le_sub_right (Finset.le_sup'
      (fun j => ∑ k ∈ Finset.range (L+1), d (t+j+k)) (Finset.mem_range.mpr hi)) S).trans
      (le_max_left _ _)
  have hpartial : ∀ n ≤ L+1, ∑ i ∈ Finset.range n, a (t+L+i) ≤ B := by
    intro n
    induction n with
    | zero => intro hn; simpa using hB
    | succ n ih =>
      intro hn
      have hnL : n ≤ L := by omega
      rw [Finset.sum_range_succ]
      by_cases hz : a (t+L+n) = 0
      · simpa [hz] using ih (by omega)
      · have hp : (∑ i ∈ Finset.range n, a (t+L+i)) ≤
            ∑ i ∈ Finset.range L, a (t+n+i) := by
          have heq : L - n + n = L := Nat.sub_add_cancel hnL
          have hsplit := Finset.sum_range_add (fun i => a (t+n+i)) (L-n) n
          rw [heq] at hsplit
          have heq' : (∑ i ∈ Finset.range n, a (t+n+(L-n+i))) =
              ∑ i ∈ Finset.range n, a (t+L+i) := by
            apply Finset.sum_congr rfl
            intro i hi
            congr 1
            omega
          rw [hsplit, heq']
          exact le_add_of_nonneg_left (Finset.sum_nonneg (fun i _ => ha _))
        have hr := hrec (t+n)
        have hind : t+n+L = t+L+n := by omega
        rw [hind] at hr
        have hdiff : 0 ≤ (∑ i ∈ Finset.range (L+1), d (t+n+i)) - S -
            ∑ i ∈ Finset.range L, a (t+n+i) := by
          by_contra hneg
          rw [max_eq_right (le_of_not_ge hneg)] at hr
          exact hz hr
        rw [max_eq_left hdiff] at hr
        exact (by linarith : (∑ i ∈ Finset.range n, a (t+L+i)) + a (t+L+n) ≤
          (∑ i ∈ Finset.range (L+1), d (t+n+i)) - S).trans (hwindow n (by omega))
  exact hpartial (L+1) le_rfl

lemma average_scan_of_blocks (P : DemandLaw) (c : Parameters) (S : ℝ≥0)
    (hblock : ∀ (ω : Sample) (m : ℕ), c.L ≤ m →
      (∑ i ∈ Finset.range (c.L+1),
        (lostSales c (cbsRun c S S ω (m+i)) (ω.1 (m+i)) : ℝ)) ≤
      max (scanDemand (fun j => ω.1 (m-c.L+j)) c.L - S) 0) :
    baseStockAverageLoss P c S ≤
      (∫⁻ d, scanExcess d c.L (S : ℝ) ∂demandPathLaw P) / ((c.L : ℝ≥0∞)+1) := by
  let C := ∫⁻ d, scanExcess d c.L (S : ℝ) ∂demandPathLaw P
  by_cases hC : C = ∞
  · change _ ≤ C / _
    rw [hC, ENNReal.top_div]
    simp
  let a : ℕ → ℝ := fun t => ∫ ω : Sample,
    (lostSales c (cbsRun c S S ω t) (ω.1 t) : ℝ) ∂sampleLaw P
  have ha0 : ∀ t, 0 ≤ a t := fun t => loss_integral_nonneg P c S S t
  have ha : ∀ t, a t ≤ mean P := fun t => loss_integral_le_mean P c S S t
  have hb : ∀ m, c.L ≤ m → ∑ i ∈ Finset.range (c.L+1), a (m+i) ≤ C.toReal := by
    intro m hm
    have hpoint : ∀ ω : Sample,
        (∑ i ∈ Finset.range (c.L+1),
          (lostSales c (cbsRun c S S ω (m+i)) (ω.1 (m+i)) : ℝ≥0∞)) ≤
        scanExcess (fun j => ω.1 (m-c.L+j)) c.L S := by
      intro ω
      have h := ENNReal.ofReal_le_ofReal (hblock ω m hm)
      simpa only [ENNReal.ofReal_sum_of_nonneg (fun i _ => NNReal.coe_nonneg _),
        ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left zero_le,
        scanExcess] using h
    have hs : ENNReal.ofReal (∑ i ∈ Finset.range (c.L+1), a (m+i)) ≤ C := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => ha0 _)]
      simp only [a, ← lintegral_loss_eq]
      rw [← lintegral_finsetSum]
      · exact (lintegral_mono hpoint).trans_eq (lintegral_scan_shift P c.L (m-c.L) S)
      · intro i hi
        have hs := measurable_cbsRun c S S (m+i)
        unfold lostSales arrival
        fun_prop
    have hh := ENNReal.toReal_mono hC hs
    rwa [ENNReal.toReal_ofReal (Finset.sum_nonneg (fun i _ => ha0 _))] at hh
  have hlim := ennreal_average_le_of_block_bound a (c.L+1) c.L (by omega)
    C.toReal (mean P) ENNReal.toReal_nonneg (le_of_lt P.positiveMean) ha0 ha hb
  unfold baseStockAverageLoss averageCost
  simp only [lintegral_loss_eq]
  change _ ≤ C / _
  convert hlim using 1
  rw [ENNReal.ofReal_div_of_pos (by positivity : 0 < ((c.L+1 : ℕ) : ℝ)),
    ENNReal.ofReal_toReal hC]
  simp [ENNReal.ofReal_add (Nat.cast_nonneg c.L) zero_le_one]

lemma average_scan_of_recursion (P : DemandLaw) (c : Parameters) (S : ℝ≥0)
    (hrec : ∀ (ω : Sample) (t : ℕ),
      (lostSales c (cbsRun c S S ω (t+c.L)) (ω.1 (t+c.L)) : ℝ) =
      max ((∑ i ∈ Finset.range (c.L+1), (ω.1 (t+i) : ℝ)) - (S : ℝ) -
        ∑ i ∈ Finset.range c.L,
          (lostSales c (cbsRun c S S ω (t+i)) (ω.1 (t+i)) : ℝ)) 0) :
    baseStockAverageLoss P c S ≤
      (∫⁻ d, scanExcess d c.L (S : ℝ) ∂demandPathLaw P) / ((c.L : ℝ≥0∞)+1) := by
  apply average_scan_of_blocks P c S
  intro ω m hm
  have h := block_from_recursion c.L (S : ℝ) (fun i => (ω.1 i : ℝ))
    (fun i => (lostSales c (cbsRun c S S ω i) (ω.1 i) : ℝ))
    (fun i => NNReal.coe_nonneg _) (hrec ω) (m-c.L)
  simpa only [Nat.sub_add_cancel hm, scanDemand, Nat.add_assoc] using h

end CBSBaseStockScanProof

open CappedBaseStock

theorem solution (P : DemandLaw) (c : Parameters) (S : ℝ≥0) :
    baseStockAverageLoss P c S ≤
      (∫⁻ d, scanExcess d c.L (S : ℝ) ∂demandPathLaw P) /
        ((c.L : ℝ≥0∞) + 1) := by
  exact CBSBaseStockScanProof.average_scan_of_recursion P c S
    (fun ω t => bs_loss_recursion c S ω t)
