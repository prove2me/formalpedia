-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.covariant_raising
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:51:17.687858+00:00
-- url     : https://prove2.me/submissions/dd7748f3-9b9d-4691-bc7f-6a6e512b67ae

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliAbstractCharacter
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_IsPol_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_covUp_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ


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
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Qr.CovUp := by
  intro V _ _ n E η hE hη m hm v hv
  cases n with
  | zero => exact ⟨fun i => i.elim0, fun x => x.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ N =>
    have hs : ∀ a : Fin (N + 1), (Formalism.FourierDecayAlt.Q.skip1 a : Fin N → Fin (N + 1)) = a.succAbove := by
      intro a
      funext j
      have hc : (j.castSucc < a ↔ (j : ℕ) < a) := by rw [Fin.lt_def, Fin.coe_castSucc]
      unfold Formalism.FourierDecayAlt.Q.skip1 Fin.succAbove
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd (hc.mpr h1) h2
      · exact absurd (hc.mp h2) h1
      · rfl
    obtain ⟨Ψ, h1, h2, h3⟩ := Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.covUp_succ E η hE hη m hm v hv
    refine ⟨Ψ, h1, h2, fun i x u => ?_⟩
    simp only [hs]
    exact h3 i x u
end Formalism.FourierDecayAlt.P
