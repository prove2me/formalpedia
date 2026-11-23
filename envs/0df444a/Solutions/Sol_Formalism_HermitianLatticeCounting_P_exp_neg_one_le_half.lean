-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.exp_neg_one_le_half
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T03:06:12.905829+00:00
-- url     : https://prove2.me/submissions/a2ca270b-4cbb-49fc-a699-6bab16185552

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P

theorem Formalism.HermitianLatticeCounting.P.exp_neg_one_le_half : Real.exp (-1) ≤ 1 / 2 := by
  have h := Real.add_one_le_exp 1
  rw [Real.exp_neg, inv_eq_one_div]
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)


theorem solution : Real.exp (-1) ≤ 1 / 2 := Formalism.HermitianLatticeCounting.P.exp_neg_one_le_half
