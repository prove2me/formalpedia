-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.ad_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:23:29.004116+00:00
-- url     : https://prove2.me/submissions/fc885d38-8a84-4500-8e93-d0e5e1cba949

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RepIntCastMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BridgeQminor
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_ev_Tm_Lf
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_bridge_qminor
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_sk_perm
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_sk_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_rep_Ead
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_ev_Tm_Ead
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_qminor_Ead

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
    (Op : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)) (hLop : HL Op)
    {P Q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hQP : Q * P = 1)
    (hE : ∀ c d (φ : Mat k r → E), CkOn 1 (GV k r) φ → ∀ g ∈ GV k r,
      Op c d φ g = ∑ a, ∑ b, (P a c * Q d b) • Eop a b φ g)
    {t : ℕ} (e : Fin t ≃ Fin (2 * r + k + 1)) (u : ℂ) (f : Mat k r → E) (hf : CkOn ((t : ℕ) : ℕ∞) (GV k r) f) :
    ∀ g ∈ GV k r, qminorOp Op e e u f g = qminorOp Eop e e u f g := by
  intro g hg
  have hΛ : ∀ c d, Rep 1 (Ead (Lf k r E) P Q c d) := fun c d => rep_Ead P Q c d
  have hT : ∀ v c d (φ : Mat k r → E), CkOn 1 (GV k r) φ → ∀ g ∈ GV k r,
      ev Eop (Tm (Ead (Lf k r E) P Q) v c d) φ g = Formalism.QuantumDeterminants.Top Op v c d φ g := by
    intro v c d φ hφ g hg
    simp only [ev_Tm_Ead, Formalism.QuantumDeterminants.Top, hE c d φ hφ g hg]
  have hA' := bridge_qminor Eop hC hL hA hS hΛ Op hLop hT (⇑e) (⇑e) u f hf g hg
  have hB' := bridge_qminor Eop hC hL hA hS (fun c d => rep_Lf_lemma c d) Eop hL
    (fun v c d φ _ g _ => ev_Tm_Lf Eop v c d φ g) (⇑e) (⇑e) u f hf g hg
  rw [← hA', ← hB', qminor_Ead (Lf k r E) hQP e u]
  have hlin : ev Eop (P.det • ∑ β : Fin t → Fin (2 * r + k + 1),
      (∏ j, Q (e j) (β j)) • qminor (Lf k r E) (⇑e) β u) f g =
      P.det • ∑ β : Fin t → Fin (2 * r + k + 1),
        (∏ j, Q (e j) (β j)) • ev Eop (qminor (Lf k r E) (⇑e) β u) f g := by
    simp only [ev, LinearMap.smul_apply, LinearMap.sum_apply, Finset.sum_apply, Pi.smul_apply]
  rw [hlin, ← Equiv.sum_comp (Equiv.arrowCongr (Equiv.refl (Fin t)) e)]
  simp only [Equiv.arrowCongr_apply, Equiv.refl_symm, Equiv.coe_refl, Function.comp_id, Function.comp_apply]
  have hac : ∀ γ : Fin t → Fin t, (Equiv.arrowCongr (Equiv.refl (Fin t)) e) γ = ⇑e ∘ γ := fun γ => rfl
  simp only [hac]
  have hsplit : ∀ F : (Fin t → Fin t) → E, (∀ γ, ¬ Function.Injective γ → F γ = 0) →
      ∑ γ, F γ = ∑ τ : Equiv.Perm (Fin t), F ⇑τ := by
    classical
    intro F hF
    rw [← Finset.sum_subset
      (Finset.subset_univ (Finset.univ.image fun τ : Equiv.Perm (Fin t) => (⇑τ : Fin t → Fin t))) ?_]
    · rw [Finset.sum_image]
      intro τ₁ _ τ₂ _ h
      exact Equiv.coe_fn_injective h
    · intro γ _ hγ
      apply hF
      intro hinj
      apply hγ
      exact Finset.mem_image.mpr
        ⟨Equiv.ofBijective γ (Finite.injective_iff_bijective.mp hinj), Finset.mem_univ _, rfl⟩
  have hz : ∀ γ : Fin t → Fin t, ¬ Function.Injective γ →
      (∏ j, Q (e j) (e (γ j))) • ev Eop (qminor (Lf k r E) (⇑e) (⇑e ∘ γ) u) f g = 0 := by
    intro γ hγ
    rw [sk_zero Eop hC hL hA hS hG (⇑e) (⇑e ∘ γ) u f hf (fun h => hγ (Function.Injective.of_comp h)) g hg,
      smul_zero]
  rw [hsplit _ hz]
  have hp : ∀ τ : Equiv.Perm (Fin t), ev Eop (qminor (Lf k r E) (⇑e) (⇑e ∘ ⇑τ) u) f g =
      ((Equiv.Perm.sign τ : ℤ) : ℂ) • ev Eop (qminor (Lf k r E) (⇑e) (⇑e) u) f g :=
    fun τ => sk_perm Eop hC hL hA hS hG (⇑e) u f hf τ (⇑e) g hg
  simp only [hp, smul_smul, ← Finset.sum_smul]
  have hdet : ∑ τ : Equiv.Perm (Fin t), (∏ j, Q (e j) (e (τ j))) * ((Equiv.Perm.sign τ : ℤ) : ℂ) = Q.det := by
    rw [← Matrix.det_submatrix_equiv_self e Q, ← Matrix.det_transpose, Matrix.det_apply]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp [Matrix.submatrix_apply, Matrix.transpose_apply, Units.smul_def, zsmul_eq_mul, mul_comm]
  have h1 : P.det * Q.det = 1 := by
    rw [mul_comm, ← Matrix.det_mul, hQP, Matrix.det_one]
  rw [hdet, h1, one_smul]
end Formalism.FourierDecayAlt.P.JFxE
