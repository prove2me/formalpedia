-- Prove2me | solution 6 for AvramDividend.Classical.local_verification
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T00:06:12.607159+00:00
-- url     : https://prove2.me/submissions/abd6791a-8dd0-4a84-9b27-f1e2108c1643
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification_from_uniform_truncated_hjb_budget
import Theorems.Thm_AvramDividend_Classical_verification_candidate_nonneg_before_ruin
import Theorems.Thm_AvramDividend_Classical_local_verification_capped_admissible_jump_bound
import Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_bv_stochastic_core
import Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_ubv_stochastic_core

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ max (X.generator w y - q * w y) (1 - deriv w y) = 0) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C → valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
      (C = ⊤ → ∀ x : ℝ, 0 ≤ x → valueFunction X q x ≤ ENNReal.ofReal (w x)) := by
  have hgen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0 := by
    intro y hy hyC
    refine ⟨(hw_hjb y hy hyC).1, ?_⟩
    calc
      X.generator w y - q * w y ≤
          max (X.generator w y - q * w y) (1 - deriv w y) :=
        le_max_left _ _
      _ = 0 := (hw_hjb y hy hyC).2
  have hgrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y := by
    intro y hy hyC
    have hh : 1 - deriv w y ≤ (0 : ℝ) := by
      calc
        1 - deriv w y ≤
            max (X.generator w y - q * w y) (1 - deriv w y) :=
          le_max_right _ _
        _ = 0 := (hw_hjb y hy hyC).2
    exact sub_nonpos.mp hh
  have hbudget : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
      ∀ n : ℕ,
        (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
          ENNReal.ofReal (w x) := by
    intro x hx hxc D hD n
    have hnonneg : ∀ ω (t : ℝ≥0), 0 < t →
        (t : ℝ≥0∞) < ruinTime X x D ω →
        0 ≤ w (riskProcess X x D t ω) := by
      intro ω t ht hru
      exact verification_candidate_nonneg_before_ruin
        X q w C hw_cont hw0 hw_smooth hw_hjb x D hD ω t ht hru
    have hjump : ∀ ω (t : ℝ≥0),
        (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
        rightLimit D t ω - D t ω ≤
          w (riskProcess X x D t ω) -
            w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)) := by
      intro ω t ht
      exact local_verification_capped_admissible_jump_bound
        X x q w C hw_cont hw_smooth hw_hjb D hD hxc ω t ht
    by_cases hBV : X.BoundedVariation
    · exact admissible_cap_truncated_bv_stochastic_core
        X hX hBV q hq w C hw_cont hw_neg (hw_smooth.2 hBV)
        hgen hgrad x hxc D hD hnonneg hjump (n : ℝ) (by positivity)
    · exact admissible_cap_truncated_ubv_stochastic_core
        X hX hBV q hq w C hw_cont hw_neg (hw_smooth.1 hBV)
        hgen hgrad x hxc D hD hnonneg hjump (n : ℝ) (by positivity)
  exact local_verification_from_uniform_truncated_hjb_budget X q w C hbudget
