-- Prove2me | solution 1 for DiazModulus.pi_sq_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T11:01:33.694053+00:00
-- url     : https://prove2.me/submissions/21abc5e3-f9fd-49d7-952f-1582a6646a9a

import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_pi_transcendental

open Complex ComplexConjugate

theorem solution : Transcendental ℚ ((Real.pi ^ 2 : ℝ) : ℂ) := by
  intro h
  refine DiazModulus.pi_transcendental ?_
  refine IsAlgebraic.of_pow (n := 2) (by norm_num) ?_
  simpa using h
