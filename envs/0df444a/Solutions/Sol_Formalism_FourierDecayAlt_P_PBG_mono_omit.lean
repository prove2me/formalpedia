-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBG.mono_omit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:44:35.826153+00:00
-- url     : https://prove2.me/submissions/7edb6053-e3f2-41f4-a803-89052ebaec41

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainFirstIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGHead
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pe_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ps_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_uniq_mono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.pe_val
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.ps_val



set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.SignAntidiagonal
namespace Formalism.FourierDecayAlt.P.PBG
theorem _root_.solution {k r m : ℕ} (hm : m + 1 ≤ r) (c : Fin m → Fin (2 * r + k + 1)) (hc : StrictMono c)
    (hlt : ∀ l, (c l).val < m + 1) : ∃ l0 : Fin (m + 1), c = xR k r (m + 1) hm ∘ l0.succAbove := by
  have hex : ∃ l0 : Fin (m + 1), ∀ l, (c l).val ≠ l0.val := by
    by_contra hne
    push Not at hne
    choose f hf using hne
    have hinj : Function.Injective f := by
      intro a b hab
      apply Fin.ext
      have := hf a; have := hf b; rw [hab] at *; omega
    have := Fintype.card_le_of_injective f hinj
    simp at this
  obtain ⟨l0, hl0⟩ := hex
  refine ⟨l0, ?_⟩
  apply uniq_mono _ _ ?_ hc
  · intro l
    have h1 : (⟨(c l).val, hlt l⟩ : Fin (m + 1)) ≠ l0 := by
      intro h; apply hl0 l; rw [← h]
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq h1
    refine ⟨j, ?_⟩
    ext
    simp only [Function.comp_apply, xR, eI, Fin.val_castLE]
    rw [hj]
  · exact (fun a b hab => by simp only [Function.comp_apply, xR, eI]; exact Fin.strictMono_succAbove l0 hab)
end Formalism.FourierDecayAlt.P.PBG
