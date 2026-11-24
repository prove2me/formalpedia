-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.C2x2.monomialMatrix_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:00:01.242381+00:00
-- url     : https://prove2.me/submissions/aba1731a-ee76-488c-9a24-7c713d226d5b

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
theorem _root_.solution (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0) :
    (C2.monoP w d)⁻¹ = C2.monoP w.symm (fun i => (d (w.symm i))⁻¹) :=
  Matrix.inv_eq_left_inv (monomialMatrix_inv_left w d hd)
end Formalism.FourierDecayAlt.P.C2x2
