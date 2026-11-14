-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a60_original_zerojump_gaussian_centered_increment_positive_mgf_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:37:13.292125+00:00
-- url     : https://prove2.me/submissions/bbe9c868-77ad-49ad-990a-30377b9eb372

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_normalised_increment_mgf_matches_gaussian
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual zero-jump source centred deterministic increment has the exact positive Gaussian exponential moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (s t : ℝ≥0) (hst : s ≤ t)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫ ω, Real.exp
      (θ * (((X.X t ω - X.X s ω) -
        ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ)) ∂P) =
    Real.exp (((t - s : ℝ≥0) : ℝ) * θ^2 / 2) := by
  have hMgf :=
    avram_p4_a_gaussian_original_normalised_increment_mgf_matches_gaussian
      X X hν rfl hσ s t hst θ hθ
  calc
    (∫ ω, Real.exp (θ * (((X.X t ω - X.X s ω) -
        ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ)) ∂P) =
        ProbabilityTheory.mgf
          (fun ω => ((X.X t ω - X.X s ω) -
            ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ) P θ := rfl
    _ = ProbabilityTheory.mgf id
        (ProbabilityTheory.gaussianReal 0 (t - s)) θ := hMgf
    _ = Real.exp (((t - s : ℝ≥0) : ℝ) * θ^2 / 2) := by
      rw [ProbabilityTheory.mgf_id_gaussianReal]
      simp
