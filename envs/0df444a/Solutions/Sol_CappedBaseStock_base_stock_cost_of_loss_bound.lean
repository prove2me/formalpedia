-- Prove2me | solution 1 for CappedBaseStock.base_stock_cost_of_loss_bound
-- status  : ACCEPTED   (prove)
-- author  : @StellaXin
-- created : 2026-09-08T02:46:01.98572+00:00
-- url     : https://prove2.me/submissions/595c22a1-fde4-44f2-b9e3-a977575e7101

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

-- Proven component: Solutions/Sol_CappedBaseStock_base_stock_cost_of_loss_bound.lean
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators
namespace CBSBaseStockCostProof
open CappedBaseStock CBSBaseStockIntegration

lemma affine_limsup_bound (x y : ℕ → ℝ) (a b ell : ℝ)
    (hb : 0 < b) (hell : 0 ≤ ell)
    (hxy : ∀ n, x n ≤ a + b * y n)
    (hy : limsup (fun n => ENNReal.ofReal (y n)) atTop ≤ ENNReal.ofReal ell) :
    limsup (fun n => ENNReal.ofReal (x n)) atTop ≤ ENNReal.ofReal (a + b * ell) := by
  apply ENNReal.le_of_forall_pos_le_add
  intro eps heps _
  have heps' : 0 < (eps : ℝ) := by exact_mod_cast heps
  have hdelta : 0 < (eps : ℝ) / b := div_pos heps' hb
  have hupper : limsup (fun n => ENNReal.ofReal (y n)) atTop <
      ENNReal.ofReal (ell + (eps : ℝ) / b) := by
    apply lt_of_le_of_lt hy
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  apply limsup_le_of_le (by isBoundedDefault)
  filter_upwards [eventually_lt_of_limsup_lt hupper] with n hn
  have hyn : y n < ell + (eps : ℝ) / b :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mp hn
  have hx : x n ≤ a + b * ell + (eps : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hyn.le hb.le
    have hcancel : b * ((eps : ℝ) / b) = eps := by field_simp
    nlinarith [hxy n]
  calc
    ENNReal.ofReal (x n) ≤ ENNReal.ofReal (a + b * ell + (eps : ℝ)) :=
      ENNReal.ofReal_le_ofReal hx
    _ ≤ ENNReal.ofReal (a + b * ell) + ENNReal.ofReal (eps : ℝ) := ENNReal.ofReal_add_le
    _ = _ := by simp

lemma average_loss_eq (P : DemandLaw) (c : Parameters) (S : ℝ≥0) :
    baseStockAverageLoss P c S = limsup (fun T : ℕ => ENNReal.ofReal
      ((∑ t ∈ Finset.range (T + 1),
        ∫ ω : Sample, (lostSales c (cbsRun c S S ω t) (ω.1 t) : ℝ) ∂sampleLaw P) /
        ((T : ℝ) + 1))) atTop := by
  unfold baseStockAverageLoss averageCost
  congr 1
  funext T
  simp_rw [lintegral_loss_eq]
  rw [ENNReal.ofReal_div_of_pos (by positivity),
    ENNReal.ofReal_sum_of_nonneg (fun t ht => loss_integral_nonneg P c S S t)]
  rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  simp

lemma filled_add_loss (c : Parameters) (s : State c.L) (d : ℝ≥0) :
    (filledDemand c s d : ℝ) + (lostSales c s d : ℝ) = d := by
  unfold filledDemand lostSales
  rcases le_total d (s.1 + arrival c s) with h | h
  · rw [min_eq_left h, tsub_eq_zero_of_le h]
    simp
  · rw [min_eq_right h, NNReal.coe_sub h]
    ring

lemma cost_bound_from_pathwise (P : DemandLaw) (c : Parameters) (S : ℝ≥0)
    (hInv : ∀ ω t, (cbsRun c S S ω t).1 ≤ S)
    (hTotal : ∀ (ω : Sample) (N : ℕ),
      (∑ t ∈ Finset.range N, ((cbsRun c S S ω (t + 1)).1 : ℝ)) ≤
      (N : ℝ) * S - ((c.L : ℝ) + 1) *
        (∑ t ∈ Finset.range N, (filledDemand c (cbsRun c S S ω t) (ω.1 t) : ℝ)))
    (ell : ℝ) (hell : 0 ≤ ell)
    (hloss : baseStockAverageLoss P c S ≤ ENNReal.ofReal ell) :
    baseStockCost P c S ≤ ENNReal.ofReal
      (c.h * ((S : ℝ) - ((c.L : ℝ) + 1) * mean P) +
        (c.p + c.h * ((c.L : ℝ) + 1)) * ell) := by
  let H (t : ℕ) (ω : Sample) : ℝ := (cbsRun c S S ω (t + 1)).1
  let Y (t : ℕ) (ω : Sample) : ℝ := lostSales c (cbsRun c S S ω t) (ω.1 t)
  let D (t : ℕ) (ω : Sample) : ℝ := ω.1 t
  let C (t : ℕ) (ω : Sample) : ℝ := c.h * H t ω + c.p * Y t ω
  have hH (t : ℕ) : Integrable (H t) (sampleLaw P) := by
    refine (integrable_const (S : ℝ)).mono' ?_ ?_
    · have hs := measurable_cbsRun c S S (t + 1)
      exact (hs.fst.coe_nnreal_real).aestronglyMeasurable
    · filter_upwards [] with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
      exact_mod_cast hInv ω (t + 1)
  have hY (t : ℕ) : Integrable (Y t) (sampleLaw P) := loss_integrable P c S S t
  have hD (t : ℕ) : Integrable (D t) (sampleLaw P) := demand_integrable P t
  have hC (t : ℕ) : Integrable (C t) (sampleLaw P) :=
    ((hH t).const_mul c.h).add ((hY t).const_mul c.p)
  have hCnonneg (t : ℕ) (ω : Sample) : 0 ≤ C t ω := by
    dsimp [C, H, Y]
    exact add_nonneg (mul_nonneg c.holding_pos.le (NNReal.coe_nonneg _))
      (mul_nonneg c.penalty_pos.le (NNReal.coe_nonneg _))
  have hfinite (N : ℕ) :
      (∑ t ∈ Finset.range N, ∫ ω, C t ω ∂sampleLaw P) ≤
      (N : ℝ) * (c.h * ((S : ℝ) - ((c.L : ℝ) + 1) * mean P)) +
        (c.p + c.h * ((c.L : ℝ) + 1)) *
          (∑ t ∈ Finset.range N, ∫ ω, Y t ω ∂sampleLaw P) := by
    have hsumH := integrable_finsetSum (Finset.range N) (fun t _ => hH t)
    have hsumD := integrable_finsetSum (Finset.range N) (fun t _ => hD t)
    have hsumY := integrable_finsetSum (Finset.range N) (fun t _ => hY t)
    have hint := integral_mono
      (hsumH.add (hsumD.const_mul ((c.L : ℝ) + 1)))
      ((integrable_const ((N : ℝ) * S)).add (hsumY.const_mul ((c.L : ℝ) + 1)))
      (show ∀ ω, (∑ t ∈ Finset.range N, H t ω) +
        ((c.L : ℝ) + 1) * (∑ t ∈ Finset.range N, D t ω) ≤
        (N : ℝ) * S + ((c.L : ℝ) + 1) * (∑ t ∈ Finset.range N, Y t ω) from by
        intro ω
        have hid : (∑ t ∈ Finset.range N, D t ω) =
            (∑ t ∈ Finset.range N,
              (filledDemand c (cbsRun c S S ω t) (ω.1 t) : ℝ)) +
            (∑ t ∈ Finset.range N, Y t ω) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro t ht
          exact (filled_add_loss c _ _).symm
        rw [hid]
        have hh := hTotal ω N
        dsimp [H]
        nlinarith)
    simp only [Pi.add_apply] at hint
    rw [integral_add hsumH (hsumD.const_mul _),
      integral_add (integrable_const _) (hsumY.const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul,
      integral_finsetSum _ (fun t _ => hH t),
      integral_finsetSum _ (fun t _ => hD t),
      integral_finsetSum _ (fun t _ => hY t)] at hint
    simp [D, demand_integral] at hint
    have hceq : (∑ t ∈ Finset.range N, ∫ ω, C t ω ∂sampleLaw P) =
        c.h * (∑ t ∈ Finset.range N, ∫ ω, H t ω ∂sampleLaw P) +
        c.p * (∑ t ∈ Finset.range N, ∫ ω, Y t ω ∂sampleLaw P) := by
      simp only [C, integral_add ((hH _).const_mul _) ((hY _).const_mul _),
        integral_const_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hceq]
    nlinarith [mul_le_mul_of_nonneg_left hint c.holding_pos.le]
  have hperiod (t : ℕ) (ω : Sample) :
      periodCost c (cbsRun c S S ω t) (ω.1 t) = ENNReal.ofReal (C t ω) := by
    have hpos := c.holding_pos.le
    have ppos := c.penalty_pos.le
    dsimp [C, H, Y, periodCost, cbsRun, step]
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul c.holding_pos.le, ENNReal.ofReal_mul c.penalty_pos.le]
    simp
  have hcosteq : baseStockCost P c S = limsup (fun T : ℕ => ENNReal.ofReal
      ((∑ t ∈ Finset.range (T + 1), ∫ ω, C t ω ∂sampleLaw P) / ((T : ℝ) + 1))) atTop := by
    unfold baseStockCost cbsCost averageCost
    simp_rw [hperiod, ← ofReal_integral_eq_lintegral_ofReal (hC _) (Eventually.of_forall (hCnonneg _))]
    congr 1
    funext T
    rw [ENNReal.ofReal_div_of_pos (by positivity),
      ENNReal.ofReal_sum_of_nonneg (fun t _ => integral_nonneg (hCnonneg t)),
      ENNReal.ofReal_add (by positivity) (by positivity)]
    simp
  rw [hcosteq]
  apply affine_limsup_bound _
    (fun T => (∑ t ∈ Finset.range (T + 1), ∫ ω, Y t ω ∂sampleLaw P) / ((T : ℝ) + 1))
    _ _ ell (by have := c.holding_pos; have := c.penalty_pos; positivity) hell
  · intro T
    have hN : 0 < (T : ℝ) + 1 := by positivity
    have hb := (div_le_div_of_nonneg_right (hfinite (T + 1)) hN.le)
    push_cast at hb
    convert hb using 1 <;> first | rfl | (field_simp [ne_of_gt hN])
  · simpa only [average_loss_eq, Y] using hloss

end CBSBaseStockCostProof

open CappedBaseStock

theorem solution (P : DemandLaw) (c : Parameters)
    (S : ℝ≥0) (ell : ℝ) (hell : 0 ≤ ell)
    (hloss : baseStockAverageLoss P c S ≤ ENNReal.ofReal ell) :
    baseStockCost P c S ≤ ENNReal.ofReal
      (c.h * ((S : ℝ) - ((c.L : ℝ) + 1) * mean P) +
        (c.p + c.h * ((c.L : ℝ) + 1)) * ell) := by
  exact CBSBaseStockCostProof.cost_bound_from_pathwise P c S
    (fun ω t => bs_inventory_le c S ω t)
    (fun ω N => bs_total_inventory_bound c S ω N) ell hell hloss
