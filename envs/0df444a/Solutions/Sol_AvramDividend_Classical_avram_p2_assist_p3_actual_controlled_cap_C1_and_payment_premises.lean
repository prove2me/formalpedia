-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_assist_p3_actual_controlled_cap_C1_and_payment_premises
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:04:12.695277+00:00
-- url     : https://prove2.me/submissions/c549e705-0949-46ee-92d7-e564cf908181

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p2_assist_p3_original_source_cap_C1_grid_premises
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_alltime_caplinear_dividend_jump_drop
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original X and admissible D meet the complete cap-continuation P3-F premises. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici (0 : ℝ)))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ContinuousOn V (Ici (0 : ℝ)) ∧
    ContDiffOn ℝ 1 V {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C} ∧
    (∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv V z) ∧
    (C = ⊤ → ∀ z : ℝ, V z = V z) ∧
    (C ≠ ⊤ → ∀ z : ℝ, V z =
      if z ≤ C.toReal then V z
      else V C.toReal + (z - C.toReal)) ∧
    (∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        V (riskProcess X x D t ω) -
          V (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) := by
  obtain ⟨hcont, hsmooth, hgrad, htop, hfinite⟩ :=
    avram_p2_assist_p3_original_source_cap_C1_grid_premises
      C w V hVtop hVfinite hw_cont hw_smooth hw_grad
  refine ⟨hcont, hsmooth, hgrad, htop, hfinite, ?_⟩
  intro ω t ht
  exact avram_wave6_05_actual_alltime_caplinear_dividend_jump_drop
    X x C hC w V hw_cont hw_smooth hw_grad
    hVtop hVfinite D hD ω t ht
