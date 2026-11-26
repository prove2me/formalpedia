-- Prove2me | solution 1 for FourierJacobi.Algebra.region_numerators_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:08:50.821807+00:00
-- url     : https://prove2.me/submissions/87681252-56c7-4939-9adc-01e0ce5093d6

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_FourierJacobi_Algebra_RegionSum
import Theorems.Thm_FourierJacobi_Algebra_raw_numerators_sum

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 8000000
namespace FourierJacobi.Algebra
theorem _root_.solution (t d U V : K) (hd : d ≠ 0) :
    (∑ i : Fin 50, rawRegionNumerators t d U V
      (1 - d * V * t) (1 - V * t / d)
      (1 - V ^ 2 * t ^ 2) (1 - U * t ^ 2) (1 - U * t ^ 4) i) =
    (1 - V ^ 2 * t ^ 2) * (1 - U * t ^ 2) * (1 - U * t ^ 4) *
      kernelNumerator t d U V := by
  rw [raw_numerators_sum]
  unfold rawNumeratorSum kernelNumerator
  field_simp
  ring
end FourierJacobi.Algebra
