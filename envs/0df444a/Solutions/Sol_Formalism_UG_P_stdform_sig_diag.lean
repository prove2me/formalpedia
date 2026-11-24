-- Prove2me | solution 1 for Formalism.UG.P.stdform_sig_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:52:58.702508+00:00
-- url     : https://prove2.me/submissions/0c206833-f230-4b83-89c5-cb9648131ac0

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureExists
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureConjugationInvariant
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stdform
import Theorems.Thm_Formalism_UG_P_stdform_Q_dot
import Theorems.Thm_Formalism_UG_P_stdform_Q_reindex
import Theorems.Thm_Formalism_UG_P_stdform_normSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix
namespace Formalism.UG.P
open Formalism.UG
section Stdform
variable {n : Type} [Fintype n] [DecidableEq n]
section Emb
variable {E : Type} [Field E]
end Emb
end Stdform
section Inv
variable {n : Type} [Fintype n] [DecidableEq n] {F E : Type} [Field F] [Field E] [Algebra F E]
end Inv
section Sign
variable {n : Type} [Fintype n] [DecidableEq n]
private lemma re_conj_mul_self_eq_normSq (z : ℂ) : (starRingEnd ℂ z * z).re = Complex.normSq z := by
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring
end Sign
end Formalism.UG.P
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution {p q : ℕ} (M : Matrix n n ℂ) (e : n ≃ Fin p ⊕ Fin q)
    (P : GL (Fin p ⊕ Fin q) ℂ)
    (hP : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ * M.reindex e e *
      (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Jpq p q) (y : n → ℂ) :
    ∃ x : Fin p ⊕ Fin q → ℂ, (y ≠ 0 → x ≠ 0) ∧
      stdformQ M y = (∑ i, Complex.normSq (x (Sum.inl i))) - ∑ j, Complex.normSq (x (Sum.inr j)) := by
  have hPP : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hy' : (fun k => y (e.symm k)) = (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ (((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ (fun k => y (e.symm k))) := by
    rw [Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec]
  obtain ⟨x, hx⟩ : ∃ x, (fun k => y (e.symm k)) = (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ x := ⟨_, hy'⟩
  refine ⟨x, ?_, ?_⟩
  · intro hy h0
    apply hy
    rw [h0, Matrix.mulVec_zero] at hx
    funext i
    simpa using congrFun hx (e i)
  · rw [← stdform_Q_reindex M e y, stdform_Q_dot, hx, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP]
    simp [Jpq, dotProduct, Matrix.fromBlocks_mulVec, Fintype.sum_sum_type, Complex.re_sum, stdform_normSq,
      re_conj_mul_self_eq_normSq, sub_eq_add_neg, Matrix.neg_mulVec, Matrix.one_mulVec, Complex.normSq_apply,
      Complex.neg_re, Complex.neg_im, mul_neg, Finset.sum_neg_distrib]
end Formalism.UG.P
