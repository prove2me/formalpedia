-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.eval_prod_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:58:12.050229+00:00
-- url     : https://prove2.me/submissions/cb90c77f-04a2-4812-8f7e-60b0f92f8bca

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
theorem _root_.solution {ι : Type} (S : Finset ι) (m : ι → ℂ) (u : ℂ) :
    (∏ j ∈ S, ((Polynomial.X : ℂ[X]) + C (m j))).eval u = ∏ j ∈ S, (u + m j) := by
  simp [Polynomial.eval_prod]
end Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
