-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_zero_jump_original_past_event_centred_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:41:35.852502+00:00
-- url     : https://prove2.me/submissions/bc3d631a-0ee3-43d7-8ed7-c66e63b6090d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_centred_increment_indep_past
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_centred_increment_laplace

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original zero-jump source Laplace transform factors over past events. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕) (hν : Y.ν = 0)
    (s t : ℝ≥0) (hst : s ≤ t) (θ : ℝ) (hθ : 0 ≤ θ)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    (∫ ω in A, Real.exp
      (θ * ((Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c)) ∂P) =
      P.real A * Real.exp (((t - s : ℝ≥0) : ℝ) * (Y.σ ^ 2 * θ ^ 2 / 2)) := by
  let Z : Ω → ℝ := fun ω =>
    (Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c
  let f : ℝ → ℝ := fun z => Real.exp (θ * z)
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
  have hLaplace :
      (∫ ω, f (Z ω) ∂P) =
        Real.exp (((t - s : ℝ≥0) : ℝ) * (Y.σ ^ 2 * θ ^ 2 / 2)) := by
    simpa only [f, Z] using
      avram_p4_a_gaussian_zero_jump_original_centred_increment_laplace
        Y hν s t hst θ hθ
  calc
    _ = P.real A * (∫ ω, f (Z ω) ∂P) := by
          simpa only [f, Z] using hFactor
    _ = _ := by rw [hLaplace]
