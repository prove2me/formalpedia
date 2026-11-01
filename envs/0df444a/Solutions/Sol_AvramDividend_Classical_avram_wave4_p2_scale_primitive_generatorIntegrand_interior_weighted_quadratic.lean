-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_scale_primitive_generatorIntegrand_interior_weighted_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T12:15:26.799311+00:00
-- url     : https://prove2.me/submissions/2f4a44ca-7d82-493a-8654-b0773483c5d2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_weighted_curvature_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_generatorIntegrand_interior_tent
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_tent_gaussian_interior_remainder_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

/-- The true source primitive has a quadratic weighted interior jump section. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (r θ : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-θ*x) *
        |SpectrallyNegativeLevy.generatorIntegrand
          (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x (-r)|)
      (Ioi r) volume ∧
    (∫ x in Ioi r, Real.exp (-θ*x) *
      |SpectrallyNegativeLevy.generatorIntegrand
        (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x (-r)|) ≤
      (r^2/2) * (∫ u : ℝ, Real.exp (-θ*u) *
        |(Ioi (0 : ℝ)).indicator (deriv W) u|) := by
  let F : ℝ → ℝ := (Ioi (0 : ℝ)).indicator (deriv W)
  let U : ℝ → ℝ := fun z => ∫ t in (0 : ℝ)..z, W t
  let f : ℝ → ℝ := fun x => Real.exp (-θ*x) *
    |SpectrallyNegativeLevy.generatorIntegrand U x (-r)|
  let g : ℝ → ℝ := fun x => Real.exp (-θ*x) *
    |∫ s in (0 : ℝ)..r, (r-s) * F (x-s)|
  have hF := avram_wave4_p2_scale_primitive_weighted_curvature_L1
    X hX q hq W hW θ hθ hqθ
  have hFL1 : Integrable
      (fun u : ℝ => Real.exp (-θ*u) * |F u|) volume := by
    simpa only [neg_mul] using hF.2.2
  have hTent :=
    avram_wave3_05_tent_gaussian_interior_remainder_integrable
      F r θ (le_of_lt hr0) hθ hF.2.1 hF.1 hFL1
  have heq : EqOn f g (Ioi r) := by
    intro x hx
    change Real.exp (-θ*x) *
        |SpectrallyNegativeLevy.generatorIntegrand U x (-r)| =
      Real.exp (-θ*x) * |∫ s in (0 : ℝ)..r, (r-s) * F (x-s)|
    rw [avram_wave4_p2_scale_primitive_generatorIntegrand_interior_tent
      X hX q hq W hW r x hr0 hr1 hx]
  constructor
  · exact (integrableOn_congr_fun heq measurableSet_Ioi).2 hTent.1
  · calc
      (∫ x in Ioi r, f x) = ∫ x in Ioi r, g x :=
        setIntegral_congr_fun measurableSet_Ioi heq
      _ ≤ (r^2/2) * (∫ u : ℝ, Real.exp (-θ*u) * |F u|) := hTent.2
