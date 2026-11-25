-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.charId
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:06:08.693834+00:00
-- url     : https://prove2.me/submissions/a757bba9-af24-48c4-89f8-510b516a30a0

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliAbstractCharacter
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_ch_abstract
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_eval_prod_lin
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_deg_prod_lin
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_KK_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_Th_pol
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


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
variable {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ} (E : Fin (N + 1) → Fin (N + 1) → Module.End ℂ V)
namespace Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
theorem _root_.solution (hE : GlRel E) {m : Fin (N + 1) → ℂ} {v : V} (hv : v ∈ CapSp E m) :
    ∀ X ∈ Gd E v, Polynomial.aeval (KK E) (∏ j, ((Polynomial.X : ℂ[X]) + C (m j))) X = 0 := by
  obtain ⟨A, hA⟩ := Th_pol E
  intro X hX
  refine ch_abstract (Gd E v) (KK E) (fun Y hY => KK_mem E hE hY) (N + 1) A _ ?_ (fun u Y hY => ?_) X hX
  · have h := deg_prod_lin (Finset.univ : Finset (Fin (N + 1))) m
    simp only [Finset.card_univ, Fintype.card_fin] at h
    omega
  · rw [← hA, ← hA, star E hE hv hY u, eval_prod_lin]
    rfl
end Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
