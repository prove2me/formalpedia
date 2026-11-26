-- Prove2me | solution 1 for FourierJacobi.Algebra.coefficientIdentity6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:18:47.584076+00:00
-- url     : https://prove2.me/submissions/1c3aaaee-701b-497e-bc0e-d5ed3b0c9beb

import Definitions.Def_FourierJacobi_Algebra_WeylCoefficient5
import Definitions.Def_FourierJacobi_Algebra_WeylCoefficient6

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace FourierJacobi.Algebra
theorem _root_.solution (t a b : K) : wc0_6 t a b + wc1_6 t a b + wc2_6 t a b + wc3_6 t a b + wc4_6 t a b + wc5_6 t a b + wc6_6 t a b + wc7_6 t a b = 0 := by
  unfold wc0_6 wc1_6 wc2_6 wc3_6 wc4_6 wc5_6 wc6_6 wc7_6
  simp only [weylWeightNumerators, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk]
  simp only [wh0_0, wh0_1, wh0_2, wh0_3, wh0_4, wh1_0, wh1_1, wh1_2, wh1_3, wh1_4, wh2_0, wh2_1, wh2_2, wh2_3, wh2_4, wh3_0, wh3_1, wh3_2, wh3_3, wh3_4, wh4_0, wh4_1, wh4_2, wh4_3, wh4_4, wh5_0, wh5_1, wh5_2, wh5_3, wh5_4, wh6_0, wh6_1, wh6_2, wh6_3, wh6_4, wh7_0, wh7_1, wh7_2, wh7_3, wh7_4, wr0_0, wr0_1, wr0_2, wr0_3, wr0_4, wr0_5, wr0_6, wr1_0, wr1_1, wr1_2, wr1_3, wr1_4, wr1_5, wr1_6, wr2_0, wr2_1, wr2_2, wr2_3, wr2_4, wr2_5, wr2_6, wr3_0, wr3_1, wr3_2, wr3_3, wr3_4, wr3_5, wr3_6, wr4_0, wr4_1, wr4_2, wr4_3, wr4_4, wr4_5, wr4_6, wr5_0, wr5_1, wr5_2, wr5_3, wr5_4, wr5_5, wr5_6, wr6_0, wr6_1, wr6_2, wr6_3, wr6_4, wr6_5, wr6_6, wr7_0, wr7_1, wr7_2, wr7_3, wr7_4, wr7_5, wr7_6, weylTargetCoefficient]
  norm_num
  all_goals ring
end FourierJacobi.Algebra
