-- Prove2me | solution 1 for CappedBaseStock.finite_cap_cost_bound
-- status  : ACCEPTED   (prove)
-- author  : @StellaXin
-- created : 2026-09-08T02:19:36.428967+00:00
-- url     : https://prove2.me/submissions/99b5c6e6-86ae-44e3-991b-a2cea8b20c4b

import Theorems.Thm_CappedBaseStock_finite_cap_inventory_bound
import Theorems.Thm_CappedBaseStock_finite_cap_lost_sales_bound

/-! Proposition 2 reduces to average inventory and average lost-sales bounds.
The weighted expected-cost and Cesàro-limsup argument is proved in this file. -/

open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace CappedBaseStockFiniteCapProof
open CappedBaseStock

lemma limsup_add_le_ennreal (u v : ℕ → ℝ≥0∞) :
    limsup (fun t => u t + v t) atTop ≤ limsup u atTop + limsup v atTop := by
  calc
    _ ≤ (⨅ a, ⨅ _ : limsup u atTop < a, a) +
        (⨅ b, ⨅ _ : limsup v atTop < b, b) := by
      apply ENNReal.le_iInf₂_add_iInf₂
      intro a ha b hb
      apply limsup_le_of_le (by isBoundedDefault)
      filter_upwards [eventually_lt_of_limsup_lt ha, eventually_lt_of_limsup_lt hb]
        with t hut hvt
      exact add_le_add hut.le hvt.le
    _ = _ := by simp

lemma averageCost_weighted_le (P : DemandLaw) (f g : ℕ → Sample → ℝ≥0∞)
    (a b : ℝ≥0∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (hf : ∀ t, Measurable (f t)) (hg : ∀ t, Measurable (g t)) :
    averageCost P (fun t ω => a * f t ω + b * g t ω) ≤
      a * averageCost P f + b * averageCost P g := by
  have hT (T : ℕ) :
      (∑ t ∈ Finset.range (T + 1),
        ∫⁻ ω, a * f t ω + b * g t ω ∂sampleLaw P) / (T + 1 : ℝ≥0∞) =
      a * ((∑ t ∈ Finset.range (T + 1), ∫⁻ ω, f t ω ∂sampleLaw P) /
        (T + 1 : ℝ≥0∞)) +
      b * ((∑ t ∈ Finset.range (T + 1), ∫⁻ ω, g t ω ∂sampleLaw P) /
        (T + 1 : ℝ≥0∞)) := by
    simp_rw [lintegral_add_left ((hf _).const_mul a), lintegral_const_mul a (hf _),
      lintegral_const_mul b (hg _)]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    simp only [div_eq_mul_inv, add_mul, mul_assoc]
  unfold averageCost
  simp_rw [hT]
  calc
    _ ≤ (limsup (fun T : ℕ => a *
          ((∑ t ∈ Finset.range (T + 1), ∫⁻ ω, f t ω ∂sampleLaw P) /
            (T + 1 : ℝ≥0∞))) atTop) +
        (limsup (fun T : ℕ => b *
          ((∑ t ∈ Finset.range (T + 1), ∫⁻ ω, g t ω ∂sampleLaw P) /
            (T + 1 : ℝ≥0∞))) atTop) := limsup_add_le_ennreal _ _
    _ = _ := by rw [ENNReal.limsup_const_mul_of_ne_top ha,
      ENNReal.limsup_const_mul_of_ne_top hb]

lemma finite_cap_cost_of_moment_bounds (P : DemandLaw) (c : Parameters) (S r : ℝ≥0)
    (A B : ℝ≥0∞)
    (hI : averageCost P (fun t ω => (↑((cbsRun c S r ω (t+1)).1) : ℝ≥0∞)) ≤ A)
    (hE : averageCost P (fun t ω =>
      (↑(lostSales c (cbsRun c S r ω t) (ω.1 t)) : ℝ≥0∞)) ≤ B) :
    cbsCost P c S r ≤ ENNReal.ofReal c.h * A + ENNReal.ofReal c.p * B := by
  have hmeasI (t : ℕ) : Measurable
      (fun ω => (↑((cbsRun c S r ω (t+1)).1) : ℝ≥0∞)) :=
    ((measurable_cbsRun c S r (t+1)).fst).coe_nnreal_ennreal
  have hmeasE (t : ℕ) : Measurable
      (fun ω => (↑(lostSales c (cbsRun c S r ω t) (ω.1 t)) : ℝ≥0∞)) := by
    apply Measurable.coe_nnreal_ennreal
    unfold lostSales arrival
    have hs := measurable_cbsRun c S r t
    fun_prop
  have heq : cbsCost P c S r =
      averageCost P (fun t ω =>
        ENNReal.ofReal c.h * (↑((cbsRun c S r ω (t+1)).1) : ℝ≥0∞) +
        ENNReal.ofReal c.p * (↑(lostSales c (cbsRun c S r ω t) (ω.1 t)) : ℝ≥0∞)) := by
    rfl
  rw [heq]
  exact (averageCost_weighted_le P _ _ _ _ ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    hmeasI hmeasE).trans (add_le_add (mul_le_mul' le_rfl hI) (mul_le_mul' le_rfl hE))

end CappedBaseStockFiniteCapProof

open CappedBaseStock

/-- The exact finite-cap policy cost conclusion of Proposition 2. -/
theorem solution (P : DemandLaw) (c : Parameters) (r z : ℝ)
    (feasible : CertificateFeasible P c r z) :
    cbsCost P c (Real.toNNReal (((c.L : ℝ) + 1) * r + z)) (Real.toNNReal r) ≤
      ENNReal.ofReal ((c.h + c.p / ((c.L : ℝ) + 1)) * z +
        (2 - 1 / ((c.L : ℝ) + 1)) * c.p * (mean P - r)) := by
  have hL : 0 < (c.L : ℝ) + 1 := by positivity
  have hz : 0 ≤ z := feasible.2.2.1
  have hdelta : 0 ≤ mean P - r := sub_nonneg.mpr feasible.2.1
  have hcombined := CappedBaseStockFiniteCapProof.finite_cap_cost_of_moment_bounds
    P c (Real.toNNReal (((c.L : ℝ) + 1) * r + z)) (Real.toNNReal r)
    (ENNReal.ofReal z)
    (ENNReal.ofReal ((mean P - r) +
      (z + (c.L : ℝ) * (mean P - r)) / ((c.L : ℝ) + 1)))
    (finite_cap_inventory_bound P c r z feasible)
    (finite_cap_lost_sales_bound P c r z feasible)
  have hI : 0 ≤ c.h * z := mul_nonneg c.holding_pos.le hz
  have hE : 0 ≤ c.p * ((mean P - r) +
      (z + (c.L : ℝ) * (mean P - r)) / ((c.L : ℝ) + 1)) := by
    apply mul_nonneg c.penalty_pos.le
    positivity
  have halgebra :
      c.h * z + c.p * ((mean P - r) +
        (z + (c.L : ℝ) * (mean P - r)) / ((c.L : ℝ) + 1)) =
      (c.h + c.p / ((c.L : ℝ) + 1)) * z +
        (2 - 1 / ((c.L : ℝ) + 1)) * c.p * (mean P - r) := by
    field_simp [ne_of_gt hL]
    ring
  calc
    _ ≤ ENNReal.ofReal c.h * ENNReal.ofReal z +
        ENNReal.ofReal c.p * ENNReal.ofReal ((mean P - r) +
          (z + (c.L : ℝ) * (mean P - r)) / ((c.L : ℝ) + 1)) := hcombined
    _ = ENNReal.ofReal (c.h * z + c.p * ((mean P - r) +
          (z + (c.L : ℝ) * (mean P - r)) / ((c.L : ℝ) + 1))) := by
      rw [← ENNReal.ofReal_mul c.holding_pos.le,
        ← ENNReal.ofReal_mul c.penalty_pos.le, ← ENNReal.ofReal_add hI hE]
    _ = _ := by rw [halgebra]
