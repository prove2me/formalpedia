-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_original_masked_discounted_negative_JL_onecell_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:11:16.467958+00:00
-- url     : https://prove2.me/submissions/392b027b-e6e5-47ac-873d-6df87621a2ba

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_negative_mark_JL_cutoff_exact_kernel
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
noncomputable section

theorem solution
    (η z a S d : ℝ) (hη : 0 < η) (hηone : η < 1)
    (hz : z < 0) (ht : Prop) [Decidable ht] :
    (if ht then a * (S - (if -1 < z then z * d else 0)) else 0) +
    (if ht ∧ z ∈ Ioo (-1 : ℝ) (-η) then a * z * d else 0) =
    (if ht then a * (S - (if -η ≤ z then z * d else 0)) else 0) := by
  by_cases hclock : ht
  · simp only [hclock, if_true, true_and]
    calc
      a * (S - (if -1 < z then z * d else 0)) +
          (if z ∈ Ioo (-1 : ℝ) (-η) then a * z * d else 0) =
          a * ((S - (if -1 < z then z * d else 0)) +
            (if z ∈ Ioo (-1 : ℝ) (-η) then z * d else 0)) := by
              by_cases hcut : z ∈ Ioo (-1 : ℝ) (-η) <;>
                simp [hcut] <;> ring
      _ = a * (S - (if -η ≤ z then z * d else 0)) :=
        congrArg (fun r : ℝ => a * r)
          (AvramDividend.Classical.avram_pj_workerC_negative_mark_JL_cutoff_exact_kernel
            η z S d hη hηone hz)
  · simp [hclock]

