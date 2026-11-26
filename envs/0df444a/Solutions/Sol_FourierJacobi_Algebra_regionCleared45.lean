-- Prove2me | solution 1 for FourierJacobi.Algebra.regionCleared45
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:07:49.46479+00:00
-- url     : https://prove2.me/submissions/55cb928c-a140-46c7-b6b7-3b970f34e95d

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
    (d ^ 2 * P * N * E * F * G) * regionTerm45 t d U V P N E F G =
      regionNumerator45 t d U V P N E F G := by
  unfold regionTerm45 regionNumerator45
  field_simp
  <;> ring
end FourierJacobi.Algebra
