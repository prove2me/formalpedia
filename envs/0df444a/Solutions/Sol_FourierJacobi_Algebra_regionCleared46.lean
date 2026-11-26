-- Prove2me | solution 1 for FourierJacobi.Algebra.regionCleared46
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:07:50.086415+00:00
-- url     : https://prove2.me/submissions/a2c3c2fd-7229-4875-b31f-0637b55294d8

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_FourierJacobi_Algebra_RegionSum

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
namespace FourierJacobi.Algebra
theorem _root_.solution (t d U V P N E F G : K)
    (hd : d ≠ 0) (hP : P ≠ 0) (hN : N ≠ 0) (hE : E ≠ 0)
    (hF : F ≠ 0) (hG : G ≠ 0) :
    (d ^ 2 * P * N * E * F * G) * regionTerm46 t d U V P N E F G =
      regionNumerator46 t d U V P N E F G := by
  unfold regionTerm46 regionNumerator46
  field_simp
  <;> ring
end FourierJacobi.Algebra
