-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_scale_primitive_small_jump_full_weighted_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T12:39:01.480332+00:00
-- url     : https://prove2.me/submissions/27d75cf8-bc80-497f-b500-7d6c622a931c

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

/-- True primitive weighted x-section has global quadratic small-jump mass. -/
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
      (Ioi (0 : ℝ)) volume ∧
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) *
      |SpectrallyNegativeLevy.generatorIntegrand
        (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x (-r)|) ≤
      W 1 * r^2 + (r^2/2) * (∫ u : ℝ, Real.exp (-θ*u) *
        |(Ioi (0 : ℝ)).indicator (deriv W) u|) := by
  let f : ℝ → ℝ := fun x => Real.exp (-(θ*x)) *
    |SpectrallyNegativeLevy.generatorIntegrand
      (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x (-r)|
  have hCross :=
    avram_wave4_p2_scale_primitive_generatorIntegrand_crossing_weighted_quadratic
      X q W hW r θ hr0 hr1 hθ
  have hInterior :=
    avram_wave4_p2_scale_primitive_generatorIntegrand_interior_weighted_quadratic
      X hX q hq W hW r θ hr0 hr1 hθ hqθ
  have hIntI : IntegrableOn f (Ioi r) volume := by
    simpa only [neg_mul] using hInterior.1
  have hIntB :
      (∫ x in Ioi r, f x) ≤
        (r^2/2) * (∫ u : ℝ, Real.exp (-θ*u) *
          |(Ioi (0 : ℝ)).indicator (deriv W) u|) := by
    simpa only [neg_mul] using hInterior.2
  have hIci : IntegrableOn f (Ici r) volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2 hIntI
  have hIcross : IntegrableOn f (Ioo (0 : ℝ) r) volume := hCross.1
  have hIunion : IntegrableOn f (Ioo (0 : ℝ) r ∪ Ici r) volume :=
    (integrableOn_union).2 ⟨hIcross, hIci⟩
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
  have hDisj : Disjoint (Ioo (0 : ℝ) r) (Ici r) := by
    rw [Set.disjoint_left]
    intro x hx hy
    exact (not_le_of_gt hx.2) hy
  refine ⟨by simpa only [hSet] using hIunion, ?_⟩
  change (∫ x in Ioi (0 : ℝ), f x) ≤ _
  calc
    (∫ x in Ioi (0 : ℝ), f x) =
      (∫ x in Ioo (0 : ℝ) r, f x) + (∫ x in Ici r, f x) := by
        rw [← hSet]
        exact setIntegral_union hDisj measurableSet_Ici hIcross hIci
    _ = (∫ x in Ioo (0 : ℝ) r, f x) + (∫ x in Ioi r, f x) := by
      rw [integral_Ici_eq_integral_Ioi]
    _ ≤ W 1 * r^2 +
        (r^2/2) * (∫ u : ℝ, Real.exp (-θ*u) *
          |(Ioi (0 : ℝ)).indicator (deriv W) u|) :=
      add_le_add hCross.2 hIntB
