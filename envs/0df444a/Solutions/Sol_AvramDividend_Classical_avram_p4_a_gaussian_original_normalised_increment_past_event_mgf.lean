-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_original_normalised_increment_past_event_mgf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:26:32.230198+00:00
-- url     : https://prove2.me/submissions/4838a1f3-064d-4512-a49b-9ef678368f4a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_centred_increment_indep_past
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_normalised_increment_mgf_matches_gaussian

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original normalised Gaussian-increment MGF factors over past events. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hν : Y.ν = 0) (hσeq : Y.σ = X.σ) (hσ : 0 < X.σ)
    (s t : ℝ≥0) (hst : s ≤ t) (θ : ℝ) (hθ : 0 ≤ θ)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    (∫ ω in A, Real.exp
      (θ * (((Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c) / X.σ)) ∂P) =
      P.real A * ProbabilityTheory.mgf id
        (ProbabilityTheory.gaussianReal 0 (t - s)) θ := by
  let Z : Ω → ℝ := fun ω =>
    (Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c
  let f : ℝ → ℝ := fun z => Real.exp (θ * (z / X.σ))
  have ht : Measurable (Y.X t) := (Y.adapted t).mono (𝓕.le t) le_rfl
  have hs : Measurable (Y.X s) := (Y.adapted s).mono (𝓕.le s) le_rfl
  have hZ : Measurable Z := by
    dsimp [Z]
    exact (ht.sub hs).sub measurable_const
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  have hIndep : Indep (𝓕 s) (MeasurableSpace.comap Z inferInstance) P := by
    simpa only [Z] using
      (avram_p4_a_gaussian_original_centred_increment_indep_past Y s t hst).symm
  have hFactor :
      (∫ ω in A, f (Z ω) ∂P) = P.real A * ∫ ω, f (Z ω) ∂P :=
    Indep.setIntegral_eq_mul (𝓕.le s) hIndep hZ.aemeasurable hA
      hf.aestronglyMeasurable
  have hMgf :
      (∫ ω, f (Z ω) ∂P) = ProbabilityTheory.mgf id
        (ProbabilityTheory.gaussianReal 0 (t - s)) θ := by
    simpa only [ProbabilityTheory.mgf, f, Z] using
      avram_p4_a_gaussian_original_normalised_increment_mgf_matches_gaussian
        X Y hν hσeq hσ s t hst θ hθ
  calc
    _ = P.real A * (∫ ω, f (Z ω) ∂P) := by
          simpa only [f, Z] using hFactor
    _ = _ := by rw [hMgf]
