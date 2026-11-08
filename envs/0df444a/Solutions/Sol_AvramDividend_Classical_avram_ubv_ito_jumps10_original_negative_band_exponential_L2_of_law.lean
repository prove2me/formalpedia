-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_ito_jumps10_original_negative_band_exponential_L2_of_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:41:34.520953+00:00
-- url     : https://prove2.me/submissions/0ca844b1-7ff3-4b0c-b584-0148578df4d6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps10_poisson_exponential_power_memLp_two

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exponential power of an intrinsic original Levy finite-band count
is square-integrable on the same original probability space. -/
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
    (a : ℝ) : MemLp (fun ω => a ^ NB ω) 2 P := by
  have hg : AEStronglyMeasurable (fun n : ℕ => a ^ n) (P.map NB) :=
    (measurable_of_countable _).aestronglyMeasurable
  have hLp : MemLp (fun n : ℕ => a ^ n) 2 (P.map NB) := by
    rw [hLaw]
    exact avram_ubv_ito_jumps10_poisson_exponential_power_memLp_two r a
  exact (memLp_map_measure_iff hg hNm.aemeasurable).mp hLp
