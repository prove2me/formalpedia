-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FreeActionExpansion.uinv_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:02:48.145028+00:00
-- url     : https://prove2.me/submissions/addbdf11-162d-4413-ad39-e59a64ac8ef6

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
variable {A S : Type} [Ring A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.FreeActionExpansion
theorem _root_.solution (s : ℂ) (i j : Fin 2) :
    ∃ c : ℂ, (Formalism.YangianSpanCharacter.T.Uinv (A := A) s) i j = algebraMap ℂ A c := by
  fin_cases i <;> fin_cases j
  · exact ⟨1, by simp [Formalism.YangianSpanCharacter.T.Uinv]⟩
  · exact ⟨0, by simp [Formalism.YangianSpanCharacter.T.Uinv]⟩
  · exact ⟨s, by simp [Formalism.YangianSpanCharacter.T.Uinv]⟩
  · exact ⟨1, by simp [Formalism.YangianSpanCharacter.T.Uinv]⟩
end Formalism.FourierDecayAlt.P.FreeActionExpansion
