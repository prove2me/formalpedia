-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.cofactor_vector_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:32.937351+00:00
-- url     : https://prove2.me/submissions/2029e14d-e8ee-46f3-b2d0-f73d0b262744

import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductPlacesInequalitySq
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LocalIntegralStructure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Formalism.HermitianLatticeCounting.LocalIntegralStructure nonZeroDivisors
set_option linter.all false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : CofactorVec := by
  intro R _ r Z
  refine ⟨fun a => ?_, ?_⟩
  · have h := congrFun (congrFun (Matrix.adjugate_mul Z) (Fin.last r)) a
    rw [Matrix.mul_apply] at h
    rw [h]
    by_cases ha : a = Fin.last r
    · subst ha
      simp
    · simp [Matrix.one_apply, ha, Ne.symm ha]
  · rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
    have h2 : ((-1 : R) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ))) = 1 := by
      rw [← two_mul, pow_mul]
      simp
    rw [h2, one_mul]
end Formalism.HermitianLatticeCounting.P
