-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_interior_generator_weighted_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T09:31:41.39899+00:00
-- url     : https://prove2.me/submissions/9dc5e215-2886-4f56-b1e9-1153ced517b2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_source_generator_interior_C2_taylor
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_tent_gaussian_interior_remainder_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral

/-- The genuine compensated source jump kernel has the sharp weighted
    quadratic bound away from the zero-reserve crossing strip. -/
theorem solution
    (W F : ℝ → ℝ) (hW : ContDiffOn ℝ 2 W (Ioi (0 : ℝ)))
    (hFpoint : ∀ u : ℝ, 0 < u → F u = iteratedDeriv 2 W u)
    (r θ : ℝ) (hr : 0 < r) (hr1 : r < 1) (hθ : 0 ≤ θ)
    (hFc : ContinuousOn F (Ioi (0 : ℝ)))
    (hFm : Measurable F)
    (hFi : Integrable
      (fun u : ℝ => Real.exp (-θ * u) * |F u|) volume) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-θ * x) *
        |SpectrallyNegativeLevy.generatorIntegrand W x (-r)|)
      (Ioi r) volume ∧
    (∫ x in Ioi r, Real.exp (-θ * x) *
      |SpectrallyNegativeLevy.generatorIntegrand W x (-r)|) ≤
      (r ^ 2 / 2) *
        (∫ u : ℝ, Real.exp (-θ * u) * |F u|) := by
  have hsource (x : ℝ) (hx : x ∈ Ioi r) :
      SpectrallyNegativeLevy.generatorIntegrand W x (-r) =
        ∫ s in (0 : ℝ)..r, (r - s) * F (x - s) := by
    have hsrc := avram_wave3_05_source_generator_interior_C2_taylor
      W hW x (-r) (by linarith) (by linarith) (by have hx' : r < x := hx; linarith)
    have hshift : x + -r = x - r := by ring
    rw [hshift] at hsrc
    rw [hsrc]
    have hreflect := intervalIntegral.integral_comp_sub_left
      (a := (0 : ℝ)) (b := r)
      (fun u : ℝ => (u - (x - r)) * iteratedDeriv 2 W u) x
    calc
      (∫ u in (x - r)..x, (u - (x - r)) * iteratedDeriv 2 W u) =
          ∫ s in (0 : ℝ)..r,
            (x - s - (x - r)) * iteratedDeriv 2 W (x - s) := by
        simpa only [sub_zero] using hreflect.symm
      _ = ∫ s in (0 : ℝ)..r,
          (r - s) * iteratedDeriv 2 W (x - s) := by
        apply intervalIntegral.integral_congr
        intro s hs
        congr 1
        ring
      _ = ∫ s in (0 : ℝ)..r, (r - s) * F (x - s) := by
        apply intervalIntegral.integral_congr
        intro s hs
        have hsr : s ≤ r := by
          have hset : s ∈ Icc (0 : ℝ) r := by
            simpa only [uIcc_of_le hr.le] using hs
          exact hset.2
        have hp : 0 < x - s := by
          exact sub_pos.mpr (lt_of_le_of_lt hsr hx)
        change (r - s) * iteratedDeriv 2 W (x - s) =
          (r - s) * F (x - s)
        rw [hFpoint (x - s) hp]
  obtain ⟨hint, hbound⟩ :=
    avram_wave3_05_tent_gaussian_interior_remainder_integrable
      F r θ hr.le hθ hFc hFm hFi
  have heq :
      (fun x : ℝ => Real.exp (-θ * x) *
        |SpectrallyNegativeLevy.generatorIntegrand W x (-r)|) =ᵐ[
        volume.restrict (Ioi r)]
      (fun x : ℝ => Real.exp (-θ * x) *
        |∫ s in (0 : ℝ)..r, (r - s) * F (x - s)|) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [hsource x hx]
  refine ⟨hint.congr heq.symm, ?_⟩
  calc
    (∫ x in Ioi r, Real.exp (-θ * x) *
      |SpectrallyNegativeLevy.generatorIntegrand W x (-r)|) =
        ∫ x in Ioi r, Real.exp (-θ * x) *
          |∫ s in (0 : ℝ)..r, (r - s) * F (x - s)| := by
      exact integral_congr_ae heq
    _ ≤ (r ^ 2 / 2) *
        (∫ u : ℝ, Real.exp (-θ * u) * |F u|) := hbound
