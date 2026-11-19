-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_negative_mark_JL_cutoff_exact_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T00:36:13.630116+00:00
-- url     : https://prove2.me/submissions/f4ff81ce-d5a4-40c3-9e89-df7ee66c7458

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
noncomputable section

theorem solution
    (η z S d : ℝ) (hηpos : 0 < η) (hηone : η < 1)
    (hzneg : z < 0) :
    (S - (if -1 < z then z * d else 0)) +
      (if z ∈ Ioo (-1 : ℝ) (-η) then z * d else 0) =
    S - (if -η ≤ z then z * d else 0) := by
  by_cases hsmall : -η ≤ z
  · have hn : ¬ z ∈ Ioo (-1 : ℝ) (-η) := by
      intro hz
      exact not_lt_of_ge hsmall hz.2
    have hgt : -1 < z := by linarith
    simp [hsmall, hn, hgt]
  · have hsmall' : z < -η := lt_of_not_ge hsmall
    by_cases hgt : -1 < z
    · have hmem : z ∈ Ioo (-1 : ℝ) (-η) := ⟨hgt, hsmall'⟩
      simp [hsmall, hgt, hmem]
    · have hn : ¬ z ∈ Ioo (-1 : ℝ) (-η) := by
        intro hz
        exact hgt hz.1
      simp [hsmall, hgt, hn]

