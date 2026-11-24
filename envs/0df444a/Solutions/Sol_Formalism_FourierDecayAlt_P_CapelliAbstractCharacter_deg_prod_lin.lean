-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.deg_prod_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:57:59.84034+00:00
-- url     : https://prove2.me/submissions/3a83777f-2a55-483b-978b-b2481bdbba0a

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliAbstractCharacter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
namespace Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
theorem _root_.solution {ι : Type} (S : Finset ι) (m : ι → ℂ) :
    (∏ j ∈ S, ((Polynomial.X : ℂ[X]) + C (m j))).natDegree ≤ S.card := by
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  simp [Polynomial.natDegree_X_add_C]
end Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
