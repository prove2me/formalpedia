-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x3.card_addChar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:41.251187+00:00
-- url     : https://prove2.me/submissions/1651d748-4f9f-42c8-ae9c-aacd7f456277

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x3
variable {K : Type} [CommRing K] {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A6x3
theorem _root_.solution (G : Type) [AddCommGroup G] [Finite G] : Nat.card (AddChar G ℂ) = Nat.card G := by
  classical
  have := Fintype.ofFinite G
  exact Nat.card_eq_fintype_card.trans (AddChar.card_eq.trans Nat.card_eq_fintype_card.symm)
end Formalism.FourierDecayAlt.P.A6x3
