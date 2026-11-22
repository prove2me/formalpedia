-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.j_pairing_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:18:30.168007+00:00
-- url     : https://prove2.me/submissions/f4409d04-829d-4f26-b2dd-c888a90d95c7

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopDegreePolynomials

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Polynomial Formalism.FourierDecayAlt.F7 Formalism.FourierDecayAlt.P.TopDegreePolynomials
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.F7.JPairing := by
  intro R M _ _ _ _ _ _ Ξ A B Av Bv s Y Y' X X'
  simp [pair2, act2, vec, Formalism.YangianSpanCharacter.T.J, Formalism.YangianSpanCharacter.T.Uinv, Fin.sum_univ_two, Matrix.mul_apply, add_smul,
    mul_smul, algebraMap_smul]
  ring
end Formalism.FourierDecayAlt.P
