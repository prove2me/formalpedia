-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_05_source_gaussian_curvature_zeroext_weighted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:52:09.021417+00:00
-- url     : https://prove2.me/submissions/ef08dfe9-0af5-432c-870c-bdbe6f1f33a3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_two_of_gaussian
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_source_gaussian_Wsecond_weighted

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A continuous positive-reserve Gaussian curvature has a measurable
    zero extension with the exact same weighted L1 mass on the full line. -/
theorem avram_gaussian_zeroext_weighted
    (F : ℝ → ℝ) (hFc : ContinuousOn F (Ioi (0 : ℝ)))
    (θ : ℝ)
    (hFl : IntegrableOn
      (fun u : ℝ => Real.exp (-θ * u) * F u)
      (Ioi (0 : ℝ)) volume) :
    let G : ℝ → ℝ := (Ioi (0 : ℝ)).piecewise F (fun _ => 0)
    Measurable G ∧ ContinuousOn G (Ioi (0 : ℝ)) ∧
      Integrable (fun u : ℝ => Real.exp (-θ * u) * |G u|) volume := by
  dsimp
  let G : ℝ → ℝ := (Ioi (0 : ℝ)).piecewise F (fun _ => 0)
  have hGm : Measurable G := by
    exact hFc.measurable_piecewise continuousOn_const measurableSet_Ioi
  have hGeq : EqOn G F (Ioi (0 : ℝ)) := by
    intro x hx
    simp [G, Set.piecewise, hx]
  have hGc : ContinuousOn G (Ioi (0 : ℝ)) :=
    hFc.congr hGeq
  have hFlabs : IntegrableOn
      (fun u : ℝ => Real.exp (-θ * u) * |F u|)
      (Ioi (0 : ℝ)) volume := by
    change Integrable
      (fun u : ℝ => Real.exp (-θ * u) * |F u|)
      (volume.restrict (Ioi 0))
    simpa only [abs_mul, abs_of_nonneg (le_of_lt (Real.exp_pos _))] using
      hFl.abs
  have hGint : Integrable
      (fun u : ℝ => Real.exp (-θ * u) * |G u|) volume := by
    have hI := (integrable_indicator_iff measurableSet_Ioi).2 hFlabs
    have hEq :
        (fun u : ℝ => Real.exp (-θ * u) * |G u|) =
          (Ioi (0 : ℝ)).indicator
            (fun u : ℝ => Real.exp (-θ * u) * |F u|) := by
      funext u
      by_cases hu : u ∈ Ioi (0 : ℝ)
      · simp [G, Set.piecewise, hu]
      · simp [G, Set.piecewise, hu]
    rw [hEq]
    exact hI
  exact ⟨hGm, hGc, hGint⟩



/-- Source Gaussian scale C² supplies continuous second curvature on
    strictly positive reserves, exactly where the Lévy Taylor kernel lives. -/
theorem avram_source_gaussian_Wsecond_continuity
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) :
    ContinuousOn (deriv (deriv W)) (Ioi (0 : ℝ)) := by
  have hW2 : ContDiffOn ℝ 2 W (Ioi 0) :=
    scaleFunction_contDiff_two_of_gaussian X hX q hq W hW hσ
  have hW1 : ContDiffOn ℝ 1 (deriv W) (Ioi 0) :=
    hW2.deriv_of_isOpen isOpen_Ioi (by norm_num)
  exact hW1.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)



/-- The actual original Gaussian q-scale curvature has a globally
    measurable zero extension with eventual weighted L1 integrability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ b : ℝ, ∀ θ : ℝ, b ≤ θ → 0 ≤ θ → q < X.ψ θ →
      let F : ℝ → ℝ :=
        (Ioi (0 : ℝ)).piecewise (deriv (deriv W)) (fun _ => 0)
      Measurable F ∧ ContinuousOn F (Ioi (0 : ℝ)) ∧
        Integrable (fun u : ℝ => Real.exp (-θ * u) * |F u|) volume := by
  obtain ⟨b, hb⟩ :=
    avram_wave3_05_source_gaussian_Wsecond_weighted
      X q hq W hW hσ φ hφ hroot
  refine ⟨b, ?_⟩
  intro θ hbθ hθ hψ
  have hC : ContinuousOn (deriv (deriv W)) (Ioi (0 : ℝ)) :=
    avram_source_gaussian_Wsecond_continuity X hX q hq W hW hσ
  have hInt : IntegrableOn
      (fun u : ℝ => Real.exp (-θ * u) * deriv (deriv W) u)
      (Ioi (0 : ℝ)) volume := by
    simpa only [neg_mul] using hb θ hbθ hθ hψ
  exact avram_gaussian_zeroext_weighted
    (deriv (deriv W)) hC θ hInt

