-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a276_original_zerojump_Gaussian_raw_increment_exponential_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:16:41.22246+00:00
-- url     : https://prove2.me/submissions/a692a313-9ec5-4f0b-9efd-faefb301b923

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a68_original_gaussian_normalised_increment_exp_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (s t : ℝ≥0) (hst : s ≤ t)
    (theta : ℝ) (hθ : 0 ≤ theta) :
    Integrable (fun ω : Ω =>
      Real.exp (theta*(X.X t ω-X.X s ω))) P := by
  let R : Ω → ℝ := fun ω => X.X t ω-X.X s ω
  let d : ℝ := ((t-s : ℝ≥0) : ℝ)*X.c
  let Z : Ω → ℝ := fun ω => (R ω-d)/X.σ
  have he : Integrable (fun ω => Real.exp ((theta*X.σ)*Z ω)) P := by
    simpa only [Z,R,d] using
      (avram_ga_a68_original_gaussian_normalised_increment_exp_integrable
        X hν hσ s t hst (theta*X.σ) (mul_nonneg hθ hσ.le))
  have heq (ω : Ω) : Real.exp (theta*R ω) =
      Real.exp (theta*d)*Real.exp ((theta*X.σ)*Z ω) := by
    rw [←Real.exp_add]
    congr 1
    dsimp [Z]
    field_simp [ne_of_gt hσ]
    ring
  change Integrable (fun ω => Real.exp (theta*R ω)) P
  exact (he.const_mul (Real.exp (theta*d))).congr
    (Filter.Eventually.of_forall (fun ω => (heq ω).symm))
