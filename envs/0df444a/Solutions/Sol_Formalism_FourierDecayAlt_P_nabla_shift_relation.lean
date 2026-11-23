-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.nabla_shift_relation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:24:01.925813+00:00
-- url     : https://prove2.me/submissions/97337ad5-fa1a-45d4-87e4-d5c5ddd3a791

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_aC_up
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_nab_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Mx4
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.M.NabSS := by
  intro P l hl
  constructor
  · ext π' π
    simp only [nabA, zbA, ggiA, sc, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Matrix.sub_apply]
    by_cases hU : Up P l π π'
    · simp only [SS, Matrix.of_apply, if_pos hU]
      rw [aC_up P l hl π π' hU]
      exact nab_step _ _ _ _
    · simp only [SS, Matrix.of_apply, if_neg hU, mul_zero, zero_mul, sub_zero]
  · ext π' π
    simp only [nabsA, zA, ggiA, sc, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Matrix.sub_apply]
    by_cases hU : Up P l π π'
    · simp only [SS, Matrix.of_apply, if_pos hU]
      rw [aC_up P l hl π π' hU]
      exact nab_step _ _ _ _
    · simp only [SS, Matrix.of_apply, if_neg hU, mul_zero, zero_mul, sub_zero]
end Formalism.FourierDecayAlt.P
