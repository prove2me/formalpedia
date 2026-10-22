-- Prove2me | solution 2 for AvramDividend.Classical.admissible_cap_nat_horizon_bound_bounded_variation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T00:38:23.09883+00:00
-- url     : https://prove2.me/submissions/47989267-ebef-47ec-bd7e-11396840ff2c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_hjb_pointwise_inequalities
import Theorems.Thm_AvramDividend_Classical_local_verification_smooth_differentiable
import Theorems.Thm_AvramDividend_Classical_verification_candidate_nonneg_before_ruin
import Theorems.Thm_AvramDividend_Classical_verification_strategy_lump_sum_drop
import Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_bv_stochastic_core

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x) := by
  intro n
  -- The two halves of the HJB inequality, separated.  The hypothesis is the
  -- combined equality `max (X.generator w y - q * w y) (1 - deriv w y) = 0`,
  -- and the Proved `hjb_pointwise_inequalities` turns it into the two
  -- separate inequalities that the verification lemmas ask for.
  have hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0 := by
    intro y hy hyC
    exact ⟨(hw_hjb y hy hyC).1, (hjb_pointwise_inequalities X q w y (hw_hjb y hy hyC).2).1⟩
  have hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y := by
    intro y hy hyC
    exact (hjb_pointwise_inequalities X q w y (hw_hjb y hy hyC).2).2
  -- The smoothness hypothesis in the disjunctive form used by the mission's
  -- verification lemmas.  The bounded-variation branch applies, so the
  -- unbounded-variation branch is vacuous.
  have hw_smooth' :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) := by
    refine ⟨fun hnbv => absurd hBV hnbv, fun _ => hw_smooth⟩
  -- The verification value is nonnegative before ruin.
  have hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω) := by
    intro ω t ht0 htru
    exact verification_candidate_nonneg_before_ruin
      X q w C hw_cont hw0 hw_smooth' hw_hjb x D hD ω t ht0 htru
  -- `ContDiffOn` gives the `DifferentiableOn` needed by the lump-sum drop.
  have hw_diff : DifferentiableOn ℝ w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    local_verification_smooth_differentiable X w C hw_smooth'
  -- Every admissible right jump of the strategy is dominated by the
  -- corresponding drop of the verification value.
  have hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)) := by
    intro ω t ht
    exact verification_strategy_lump_sum_drop
      X w C hw_cont hw_diff hw_grad x hxc D hD ω t ht
  -- The bounded-variation stochastic verification bound at the real horizon
  -- `T = n`.
  have htrunc := admissible_cap_truncated_bv_stochastic_core
    X hX hBV q hq w C hw_cont hw_neg hw_smooth hw_gen hw_grad
    x hxc D hD hw_nonneg hjump (n : ℝ) (by positivity)
  -- The natural horizon is contained in the real horizon: a payment time
  -- below `min (ruinTime) n` is below `ruinTime` and at most `n`.
  have hsub : ∀ ω : Ω,
      paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ⊆
        paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ) := by
    intro ω t ht
    have ht0 : 0 ≤ t := ht.1
    have hpay : t ∈ paymentTimes (ruinTime X x D ω) := by
      refine ⟨ht0, ?_⟩
      rcases ht.2 with hzero | hlt
      · exact Or.inl hzero
      · exact Or.inr (lt_of_lt_of_le hlt (min_le_left _ _))
    have htn : t ≤ (n : ℝ) := by
      rcases ht.2 with hzero | hlt
      · rw [hzero]
        positivity
      · have hlt' : ENNReal.ofReal t < (n : ℝ≥0∞) :=
          lt_of_lt_of_le hlt (min_le_right _ _)
        have hlt_nn : t < (n : ℝ≥0) :=
          (ENNReal.ofReal_lt_coe_iff ht0).mp hlt'
        exact le_of_lt hlt_nn
    exact ⟨hpay, htn⟩
  apply le_trans ?_ htrunc
  apply lintegral_mono
  intro ω
  apply lintegral_mono_set
  exact hsub ω
