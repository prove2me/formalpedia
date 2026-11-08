-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_ito_jumps10_original_negative_band_exponential_integrable_of_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:27:49.392204+00:00
-- url     : https://prove2.me/submissions/b9037e22-65f3-4322-9c6e-4f0a66f49809

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps10_poisson_power_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- An actual original finite-band Levy jump count inherits all real
exponential-power L1 moments once its original-space Poisson law is known. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (B : Set ℝ)
    (NB : Ω → ℕ)
    (hcount : ∀ ω, (NB ω : ℝ≥0∞) =
      ((Measure.count.restrict
        {u : ℝ≥0 | 0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 =>
          (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Set.Ioc (0 : ℝ≥0) T ×ˢ B))
    (hNm : Measurable NB)
    (r : ℝ≥0)
    (hLaw : P.map NB = poissonMeasure r)
    (a : ℝ) : Integrable (fun ω => a ^ NB ω) P := by
  have hg : AEStronglyMeasurable (fun n : ℕ => a ^ n) (P.map NB) :=
    (measurable_of_countable _).aestronglyMeasurable
  have hI : Integrable (fun n : ℕ => a ^ n) (P.map NB) := by
    rw [hLaw]
    exact avram_ubv_ito_jumps10_poisson_power_integrable r a
  exact (integrable_map_measure hg hNm.aemeasurable).mp hI
