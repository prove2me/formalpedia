-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.sk_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:08:15.529808+00:00
-- url     : https://prove2.me/submissions/ea3e2c7c-59af-47ad-bfdb-4b2cf2a9ad6a

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RepIntCastMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BridgeQminor
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_sk_perm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
namespace Formalism.FourierDecayAlt.P.JFxE
theorem _root_.solution (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) (hS : HS Eop) (hG : HGl Eop) {t : ℕ}
    (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (f : Mat k r → E) (hf : CkOn ((t : ℕ) : ℕ∞) (GV k r) f)
    (hb : ¬ Function.Injective b) : ∀ g ∈ GV k r, ev Eop (qminor (Lf k r E) a b u) f g = 0 := by
  intro g hg
  simp only [Function.Injective, not_forall] at hb
  obtain ⟨i, j, hij, hne⟩ := hb
  have hb' : b ∘ ⇑(Equiv.swap i j) = b := by
    funext x
    simp only [Function.comp_apply, Equiv.swap_apply_def]
    split_ifs <;> simp_all
  have h := sk_perm Eop hC hL hA hS hG a u f hf (Equiv.swap i j) b g hg
  rw [hb', Equiv.Perm.sign_swap hne] at h
  simp at h
  have h2 : (2 : ℂ) • ev Eop (qminor (Lf k r E) a b u) f g = 0 := by
    rw [two_smul]
    nth_rw 1 [h]
    simp
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
end Formalism.FourierDecayAlt.P.JFxE
