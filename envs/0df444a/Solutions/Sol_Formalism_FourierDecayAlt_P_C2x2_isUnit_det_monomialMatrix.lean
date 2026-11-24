-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.C2x2.isUnit_det_monomialMatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:03:30.117787+00:00
-- url     : https://prove2.me/submissions/da5cda79-a165-4ae8-bbc3-b9d84897a7b7

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_monomialMatrix_inv_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.C2x2
variable {m : ℕ}
namespace Formalism.FourierDecayAlt.P.C2x2
theorem _root_.solution (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0) : IsUnit (C2.monoP w d).det :=
  Matrix.isUnit_det_of_left_inverse (monomialMatrix_inv_left w d hd)
end Formalism.FourierDecayAlt.P.C2x2
