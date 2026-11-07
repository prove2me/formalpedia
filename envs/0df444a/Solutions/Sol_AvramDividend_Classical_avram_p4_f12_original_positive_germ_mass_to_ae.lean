-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f12_original_positive_germ_mass_to_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T19:31:33.56591+00:00
-- url     : https://prove2.me/submissions/c16f230f-48d5-4100-bb0e-9d85a0d34f80

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_DurrettProbability_Brownian
import Theorems.Thm_AvramDividend_Classical_levy_germ_zero_one_ws01f
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical DurrettProbability
open scoped NNReal ENNReal
noncomputable section

/-- The Lévy germ zero-one law upgrades positive source mass to almost-sure occurrence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (A : Set Ω) (hA : MeasurableSet[germSigma X.X] A)
    (hPos : 0 < P.real A) :
    ∀ᵐ ω ∂P, ω ∈ A := by
  letI : IsProbabilityMeasure P := X.isProbability
  rcases levy_germ_zero_one_ws01f X hA with h0 | h1
  · exfalso
    have hR : P.real A = 0 := by
      rw [Measure.real, h0]
      rfl
    linarith
  · rw [ae_iff]
    have hBm : ∀ t : ℝ≥0, Measurable (X.X t) := by
      intro t
      exact (X.adapted t).mono (𝓕.le t) le_rfl
    have hPast (s : ℝ≥0) : pastSigma X.X s ≤ mΩ := by
      unfold pastSigma
      exact iSup₂_le (fun t ht => (hBm t).comap_le)
    have hgerm : germSigma X.X ≤ mΩ := by
      unfold germSigma
      exact iInf_le_of_le (1 : ℝ≥0)
        (iInf_le_of_le (by norm_num : (0 : ℝ≥0) < 1) (hPast 1))
    have hAmb : MeasurableSet A := hgerm A hA
    have hC : P Aᶜ = 0 := (prob_compl_eq_zero_iff hAmb).mpr h1
    simpa [compl_def] using hC
