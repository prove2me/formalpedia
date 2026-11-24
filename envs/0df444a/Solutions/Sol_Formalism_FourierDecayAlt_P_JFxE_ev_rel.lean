-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.ev_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:51:37.982032+00:00
-- url     : https://prove2.me/submissions/b7536c69-9983-45e0-a06d-d3df1c1c196e

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RepIntCastMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BridgeQminor
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_ev_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Finset
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
section Bridge
variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
end Bridge
section Skew
variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
private theorem rep_Lf_lemma (a b : Fin (2 * r + k + 1)) : Rep 1 (Lf k r E a b) :=
  ⟨[(1, [(a, b)])], by simp, fun _ _ => by simp [Lf, Formalism.FourierDecayAlt.P.JFxE.ell]⟩
end Skew
section Ad
variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
end Ad
end Formalism.FourierDecayAlt.P.JFxE
end
end

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
theorem _root_.solution (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) (hS : HS Eop) (hG : HGl Eop)
    (a b c d : Fin (2 * r + k + 1)) (ψ : Mat k r → E) (hψ : CkOn 2 (GV k r) ψ) :
    ∀ g ∈ GV k r, ev Eop (rel (Lf k r E) a b c d) ψ g = 0 := by
  intro g hg
  have hLf : ∀ (a b : Fin (2 * r + k + 1)) (φ : Mat k r → E), ev Eop (Lf k r E a b) φ = Eop a b φ := by
    intro a b φ
    funext x
    simp [ev, Lf, Formalism.FourierDecayAlt.P.JFxE.ell, Phi, Fw]
  have hz : ∀ φ : Mat k r → E, ev Eop (0 : AA k r E) φ = 0 := by
    intro φ
    funext x
    simp [ev]
  have hsub : ∀ (x y : AA k r E) (φ : Mat k r → E), ev Eop (x - y) φ g = ev Eop x φ g - ev Eop y φ g := by
    intro x y φ
    simp [ev]
  have h1 := rep_Lf_lemma (k := k) (r := r) (E := E)
  have hm : ∀ a b c d : Fin (2 * r + k + 1),
      ev Eop (Lf k r E a b * Lf k r E c d) ψ g = Eop a b (Eop c d ψ) g := by
    intro a b c d
    rw [ev_mul (Eop := Eop) hC hL hA hS (h1 a b) (h1 c d) ψ hψ g hg, hLf, hLf]
  simp only [Formalism.FourierDecayAlt.P.JFxE.rel]
  rw [hsub, hsub, hsub, hm, hm, hG a b c d ψ hψ g hg]
  split_ifs <;> simp [hLf, hz]
end Formalism.FourierDecayAlt.P.JFxE
