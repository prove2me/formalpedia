-- Prove2me | solution 1 for AvramDividend.Classical.avram_a116_ae_zero_nat_count_haslaw_zero_rate_poisson_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:19:25.028849+00:00
-- url     : https://prove2.me/submissions/3ed357ac-4b1b-4c62-acfa-767488b01f3c

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (hZero : K =ᵐ[P] (fun _ : Ω => (0 : ℕ))) :
    HasLaw K (poissonMeasure (0 : ℝ≥0)) P := by
  have hMap : Measure.map K P = Measure.dirac (0 : ℕ) := calc
    Measure.map K P = Measure.map (fun _ : Ω => (0 : ℕ)) P :=
      Measure.map_congr hZero
    _ = Measure.dirac 0 := by simp
  have hPoissonZero : poissonMeasure (0 : ℝ≥0) = Measure.dirac (0 : ℕ) := by
    refine Measure.ext_of_singleton fun n => ?_
    rw [poissonMeasure_singleton, Measure.dirac_apply' 0 (measurableSet_singleton n)]
    by_cases hn : n = 0
    · subst hn
      simp
    · simp only [Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply, NNReal.coe_zero]
      rw [if_neg (fun h => hn h.symm)]
      simp [zero_pow hn]
  refine ⟨hK.aemeasurable, ?_⟩
  simpa only [hPoissonZero] using hMap
