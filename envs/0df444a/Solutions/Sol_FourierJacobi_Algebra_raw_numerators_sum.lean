-- Prove2me | solution 1 for FourierJacobi.Algebra.raw_numerators_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:08:14.540304+00:00
-- url     : https://prove2.me/submissions/0f19bca4-5a75-4c71-b6a7-dded3207af51

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
set_option maxHeartbeats 8000000
namespace FourierJacobi.Algebra
theorem _root_.solution (t d U V P N E F G : K) :
    (∑ i : Fin 50, rawRegionNumerators t d U V P N E F G i) =
      rawNumeratorSum t d U V P N E F G := by
  simp only [rawRegionNumerators, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  unfold regionNumerator0 regionNumerator1 regionNumerator2 regionNumerator3 regionNumerator4 regionNumerator5 regionNumerator6 regionNumerator7 regionNumerator8 regionNumerator9 regionNumerator10 regionNumerator11 regionNumerator12 regionNumerator13 regionNumerator14 regionNumerator15 regionNumerator16 regionNumerator17 regionNumerator18 regionNumerator19 regionNumerator20 regionNumerator21 regionNumerator22 regionNumerator23 regionNumerator24 regionNumerator25 regionNumerator26 regionNumerator27 regionNumerator28 regionNumerator29 regionNumerator30 regionNumerator31 regionNumerator32 regionNumerator33 regionNumerator34 regionNumerator35 regionNumerator36 regionNumerator37 regionNumerator38 regionNumerator39 regionNumerator40 regionNumerator41 regionNumerator42 regionNumerator43 regionNumerator44 regionNumerator45 regionNumerator46 regionNumerator47 regionNumerator48 regionNumerator49 rawNumeratorSum
  ring
end FourierJacobi.Algebra
