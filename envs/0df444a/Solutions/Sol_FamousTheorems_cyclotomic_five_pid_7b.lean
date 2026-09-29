-- Prove2me | solution 1 for FamousTheorems.cyclotomic_five_pid_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:43:32.366974+00:00
-- url     : https://prove2.me/submissions/23dea780-1dfb-4658-9510-94432d032ef8

import Mathlib

theorem solution (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {5} ℚ K] :
    IsPrincipalIdealRing (NumberField.RingOfIntegers K) :=
  IsCyclotomicExtension.Rat.five_pid K
