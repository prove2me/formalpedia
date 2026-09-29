-- Prove2me | solution 1 for BoltzmannConstant.molar_gas_constant_value
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T18:19:15.260696+00:00
-- url     : https://prove2.me/submissions/dfbaedf3-4db4-49cc-b62d-d8a7d419dd22

import Mathlib
import Definitions.Def_boltzmann_si_basics

open BoltzmannConstant in
theorem solution : R = 8.31446261815324 := by
  unfold R kB NA
  norm_num

#print axioms solution
