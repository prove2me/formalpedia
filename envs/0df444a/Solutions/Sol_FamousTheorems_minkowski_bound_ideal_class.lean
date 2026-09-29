-- Prove2me | solution 1 for FamousTheorems.minkowski_bound_ideal_class
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:21:07.138049+00:00
-- url     : https://prove2.me/submissions/5a2e3997-0ce1-4b1b-869b-c025e6480f84

import Mathlib

theorem solution {K : Type*} [Field K] [NumberField K] (C : ClassGroup (NumberField.RingOfIntegers K)) :
    ∃ I : nonZeroDivisors (Ideal (NumberField.RingOfIntegers K)), ClassGroup.mk0 I = C ∧
      (Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)) : ℝ) ≤
        (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
          (((Module.finrank ℚ K).factorial : ℝ) / (Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K *
            Real.sqrt |(NumberField.discr K : ℝ)|) :=
  NumberField.exists_ideal_in_class_of_norm_le C
