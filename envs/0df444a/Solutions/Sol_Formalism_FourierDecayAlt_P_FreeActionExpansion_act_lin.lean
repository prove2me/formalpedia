-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FreeActionExpansion.act_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:01:28.687794+00:00
-- url     : https://prove2.me/submissions/80ddde9d-0aa0-4596-9b83-7a18bf73fec4

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionUpdateSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeActionExpansion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FreeActionExpansion
open Finset Polynomial Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums
open scoped Matrix
variable {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S]
  [DecidableEq S] [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]
namespace Formalism.FourierDecayAlt.P.FreeActionExpansion
theorem _root_.solution (G : SlopeTestRemainingChoices S A) (X : Ix S → V) (P b c : A) (s : ℂ) :
    act G ((P * (b + algebraMap ℂ A s * c)) • X) = act G ((P * b) • X) + s • act G ((P * c) • X) := by
  have e : (P * (b + algebraMap ℂ A s * c)) • X = (P * b) • X + s • ((P * c) • X) := by
    rw [mul_add, add_smul, ← mul_assoc P (algebraMap ℂ A s) c, ← Algebra.commutes s P, mul_assoc,
      mul_smul (algebraMap ℂ A s) (P * c) X, algebraMap_smul]
  rw [e, act_add, act_smul]
end Formalism.FourierDecayAlt.P.FreeActionExpansion
