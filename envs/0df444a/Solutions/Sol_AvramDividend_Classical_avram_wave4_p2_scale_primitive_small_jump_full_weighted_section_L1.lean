-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_scale_primitive_small_jump_full_weighted_section_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T12:35:32.290285+00:00
-- url     : https://prove2.me/submissions/22c94a42-cba7-4cd2-82c6-7112eafa1fc4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_generatorIntegrand_crossing_weighted_quadratic
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_generatorIntegrand_interior_weighted_quadratic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

/-- The true compensated source primitive has each small-jump weighted full x-section L1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (r θ : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-(θ*x)) *
        |SpectrallyNegativeLevy.generatorIntegrand
          (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x (-r)|)
      (Ioi (0 : ℝ)) volume := by
  let f : ℝ → ℝ := fun x => Real.exp (-(θ*x)) *
    |SpectrallyNegativeLevy.generatorIntegrand
      (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x (-r)|
  have hCross : IntegrableOn f (Ioo (0 : ℝ) r) volume :=
    (avram_wave4_p2_scale_primitive_generatorIntegrand_crossing_weighted_quadratic
      X q W hW r θ hr0 hr1 hθ).1
  have hInterior : IntegrableOn f (Ioi r) volume := by
    have h :=
      (avram_wave4_p2_scale_primitive_generatorIntegrand_interior_weighted_quadratic
        X hX q hq W hW r θ hr0 hr1 hθ hqθ).1
    simpa only [neg_mul] using h
  have hRight : IntegrableOn f (Ici r) volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2 hInterior
  have hBoth : IntegrableOn f (Ioo (0 : ℝ) r ∪ Ici r) volume :=
    (integrableOn_union).2 ⟨hCross, hRight⟩
  have hSet : Ioo (0 : ℝ) r ∪ Ici r = Ioi (0 : ℝ) := by
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact hx.1
      · exact lt_of_lt_of_le hr0 hx
    · intro hx
      by_cases hxr : x < r
      · exact Or.inl ⟨hx, hxr⟩
      · exact Or.inr (le_of_not_gt hxr)
  simpa only [hSet] using hBoth
