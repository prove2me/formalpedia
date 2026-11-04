-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_original_normalised_mgf_matches_gaussian_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:58:38.116216+00:00
-- url     : https://prove2.me/submissions/f30e88a6-9f57-4776-9045-63c059dd4867

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_normalised_laplace_identity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The positive-parameter moment-generating function of the genuine
same-volatility zero-jump Levy component equals that of the standard
real Gaussian with variance `t`. This is a source-exact law-identification
bridge and does not assume a Brownian copy or a stochastic integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hν : Y.ν = 0) (hσeq : Y.σ = X.σ) (hσ : 0 < X.σ)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    ProbabilityTheory.mgf
      (fun ω => (Y.X t ω - (t : ℝ) * Y.c) / X.σ) P θ =
        ProbabilityTheory.mgf id (ProbabilityTheory.gaussianReal 0 t) θ := by
  have hLap :=
    avram_p4_a_gaussian_zero_jump_original_normalised_laplace_identity
      X Y hν hσeq hσ t θ hθ
  calc
    _ = Real.exp ((t : ℝ) * (θ ^ 2 / 2)) := by
      simpa only [ProbabilityTheory.mgf] using hLap
    _ = ProbabilityTheory.mgf id (ProbabilityTheory.gaussianReal 0 t) θ := by
      rw [ProbabilityTheory.mgf_id_gaussianReal]
      all_goals simp
      all_goals ring
