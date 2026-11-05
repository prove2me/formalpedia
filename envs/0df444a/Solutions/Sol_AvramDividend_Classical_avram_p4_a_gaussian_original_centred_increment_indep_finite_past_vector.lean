-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_original_centred_increment_indep_finite_past_vector
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:33:45.91187+00:00
-- url     : https://prove2.me/submissions/4ed8fd8e-fb17-430c-b6ad-e2abb9919ab0

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_centred_increment_indep_past

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal

/-- A centred original Levy increment is independent of every finite vector of past source observations. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (n : ℕ) (v : Fin n → ℝ≥0) (hv : ∀ i, v i ≤ s) :
    Indep
      (MeasurableSpace.comap
        (fun ω => (Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c)
        inferInstance)
      (MeasurableSpace.comap
        (fun ω => fun i : Fin n => Y.X (v i) ω)
        inferInstance) P := by
  have hcoord (i : Fin n) : Measurable[𝓕 s] (Y.X (v i)) :=
    (Y.adapted (v i)).mono (𝓕.mono (hv i)) le_rfl
  have hvec : Measurable[𝓕 s]
      (fun ω => fun i : Fin n => Y.X (v i) ω) := by
    letI : MeasurableSpace Ω := 𝓕 s
    exact measurable_pi_iff.mpr (fun i => hcoord i)
  have hLE :
      MeasurableSpace.comap
        (fun ω => fun i : Fin n => Y.X (v i) ω)
        inferInstance ≤ 𝓕 s := by
    intro A hA
    obtain ⟨B, hB, rfl⟩ := (MeasurableSpace.measurableSet_comap).1 hA
    exact hvec hB
  exact indep_of_indep_of_le_right
    (avram_p4_a_gaussian_original_centred_increment_indep_past Y s t hst) hLE
