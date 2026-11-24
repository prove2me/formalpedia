-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.sk_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:29:38.327242+00:00
-- url     : https://prove2.me/submissions/455788c0-c127-435b-9868-6bdceb40e9db

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RepIntCastMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BridgeQminor
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_ev_LMR
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_adj_formal
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ


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
theorem _root_.solution (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) (hS : HS Eop) (hG : HGl Eop) {m : ℕ}
    (a b : Fin (m + 1) → Fin (2 * r + k + 1)) (i : Fin m) (u : ℂ)
    (f : Mat k r → E) (hf : CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) f) :
    ∀ g ∈ GV k r, ev Eop (qminor (Lf k r E) a (b ∘ Equiv.swap i.castSucc i.succ) u) f g =
      - ev Eop (qminor (Lf k r E) a b u) f g := by
  intro g hg
  have hR : ∀ σ : Equiv.Perm (Fin (m + 1)),
      (Lt (Lf k r E) a b u σ i * Md (Lf k r E) a b σ i * Rt (Lf k r E) a b u σ i) (Phi Eop f) [] g = 0 :=
    fun σ => ev_LMR Eop hC hL hA hS hG a b u σ i f hf g hg
  have hR' : ∀ σ : Equiv.Perm (Fin (m + 1)),
      (((Equiv.Perm.sign σ : ℤ) : AA k r E) *
        (Lt (Lf k r E) a b u σ i * Md (Lf k r E) a b σ i * Rt (Lf k r E) a b u σ i)) (Phi Eop f) [] g = 0 := by
    intro σ
    have h0 := hR σ
    generalize Lt (Lf k r E) a b u σ i * Md (Lf k r E) a b σ i * Rt (Lf k r E) a b u σ i = P at h0 ⊢
    simp [h0]
  have h := congrArg (fun x : AA k r E => x (Phi Eop f) [] g) (adj_formal (Lf k r E) a b i u)
  simp only [LinearMap.smul_apply, LinearMap.add_apply, Pi.smul_apply, Pi.add_apply, LinearMap.sum_apply,
    Finset.sum_apply, hR', Finset.sum_const_zero] at h
  have h3 := (smul_eq_zero.mp h).resolve_left two_ne_zero
  exact eq_neg_of_add_eq_zero_left h3
end Formalism.FourierDecayAlt.P.JFxE
