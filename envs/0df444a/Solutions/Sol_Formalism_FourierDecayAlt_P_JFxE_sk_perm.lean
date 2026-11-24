-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.sk_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:51:55.037067+00:00
-- url     : https://prove2.me/submissions/3cfc936a-1bc5-4614-a4b8-3be8c30276d1

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RepIntCastMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BridgeQminor
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_sk_adj
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
    (a : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (f : Mat k r → E) (hf : CkOn ((t : ℕ) : ℕ∞) (GV k r) f)
    (τ : Equiv.Perm (Fin t)) :
    ∀ (b : Fin t → Fin (2 * r + k + 1)), ∀ g ∈ GV k r,
      ev Eop (qminor (Lf k r E) a (b ∘ τ) u) f g = ((Equiv.Perm.sign τ : ℤ) : ℂ) • ev Eop (qminor (Lf k r E) a b u) f g := by
  cases t with
  | zero =>
    intro b g hg
    have hτ : τ = 1 := Subsingleton.elim _ _
    subst hτ
    simp
  | succ m =>
    have hmem : τ ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      exact Submonoid.mem_top τ
    induction hmem using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro b g hg
      rw [sk_adj Eop hC hL hA hS hG a b i u f hf g hg, Equiv.Perm.sign_swap (Fin.castSucc_lt_succ : i.castSucc < i.succ).ne]
      simp
    | one =>
      intro b g hg
      simp
    | mul x y _ _ hx hy =>
      intro b g hg
      have e : b ∘ ⇑(x * y) = (b ∘ ⇑x) ∘ ⇑y := rfl
      rw [e, hy (b ∘ ⇑x) g hg, hx b g hg, Equiv.Perm.sign_mul]
      simp only [Units.val_mul, Int.cast_mul, mul_smul]
      rw [smul_comm]
end Formalism.FourierDecayAlt.P.JFxE
