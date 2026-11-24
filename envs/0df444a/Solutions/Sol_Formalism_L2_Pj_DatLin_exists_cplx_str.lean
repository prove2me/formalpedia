-- Prove2me | solution 1 for Formalism.L2.Pj.DatLin.exists_cplx_str
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:23:07.549249+00:00
-- url     : https://prove2.me/submissions/639763de-0728-4639-a680-14f3f4435db9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_DatMat
import Theorems.Thm_Formalism_L2_Pj_DatLin_star_mulVec_dot
import Theorems.Thm_Formalism_L2_Pj_DatLin_star_dot_self_eq
import Theorems.Thm_Formalism_L2_Pj_DatLin_sum_normSq_pos
import Theorems.Thm_Formalism_L2_Pj_DatLin_cplx_str_core

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.DatLin
open Matrix Complex
variable {m : Type} [Fintype m] [DecidableEq m]
namespace Formalism.L2.Pj.DatLin
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (p q : ℕ)
    (e : n ≃ Fin p ⊕ Fin q) (P : GL (Fin p ⊕ Fin q) ℂ)
    (hP : ((P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).map (starRingEnd ℂ))ᵀ * H.reindex e e *
      (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Matrix.fromBlocks 1 0 0 (-1)) :
    ∃ K : Matrix n n ℂ, (∀ u, K *ᵥ (K *ᵥ u) = -u) ∧
      (∀ u w, star (K *ᵥ u) ⬝ᵥ (H *ᵥ (K *ᵥ w)) = star u ⬝ᵥ (H *ᵥ w)) ∧
      (∀ u : n → ℂ, u ≠ 0 → ∃ ρ : ℝ, 0 < ρ ∧ star (K *ᵥ u) ⬝ᵥ (H *ᵥ u) = -(Complex.I * ρ)) ∧
      K.trace = Complex.I * ((p : ℂ) - q) := by
  set P0 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) with hP0
  set Q0 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
    ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) with hQ0
  set J0 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := Matrix.fromBlocks 1 0 0 (-1) with hJ0
  have hPh : (P0.map (starRingEnd ℂ))ᵀ = P0ᴴ := rfl
  rw [hPh] at hP
  have hPQ0 : P0 * Q0 = 1 := P.mul_inv
  have hQP0 : Q0 * P0 = 1 := P.inv_mul
  have hJJ0 : J0 * J0 = 1 := by
    simp [hJ0, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  set Pn := P0.submatrix e e
  set Qn := Q0.submatrix e e
  set Jn := J0.submatrix e e
  have hPQ : Pn * Qn = 1 := by rw [Matrix.submatrix_mul_equiv, hPQ0, Matrix.submatrix_one_equiv]
  have hQP : Qn * Pn = 1 := by rw [Matrix.submatrix_mul_equiv, hQP0, Matrix.submatrix_one_equiv]
  have hJ2 : Jn * Jn = 1 := by rw [Matrix.submatrix_mul_equiv, hJJ0, Matrix.submatrix_one_equiv]
  have hJh : Jnᴴ = Jn := by
    simp [Jn, hJ0, Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]
  have hH : Pnᴴ * H * Pn = Jn := by
    have hH0 : H = (H.reindex e e).submatrix e e := by
      ext i j; simp [Matrix.reindex_apply]
    rw [hH0, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hP]
  obtain ⟨h1, h2, h3, h4⟩ := cplx_str_core H Pn Qn Jn hPQ hQP hJ2 hJh hH
  refine ⟨Pn * (Complex.I • Jn) * Qn, ?_, ?_, ?_, ?_⟩
  · intro u
    rw [Matrix.mulVec_mulVec, h1, Matrix.neg_mulVec, Matrix.one_mulVec]
  · intro u w
    rw [Matrix.mulVec_mulVec, star_mulVec_dot, ← Matrix.mul_assoc, h2]
  · intro u hu
    refine ⟨∑ i, Complex.normSq ((Qn *ᵥ u) i), sum_normSq_pos ?_, ?_⟩
    · intro h0
      apply hu
      have := congrArg (Pn *ᵥ ·) h0
      simpa [Matrix.mulVec_mulVec, hPQ] using this
    · rw [star_mulVec_dot, h3, Matrix.smul_mulVec, dotProduct_smul, ← star_mulVec_dot, star_dot_self_eq,
        smul_eq_mul, neg_mul]
  · rw [h4]
    congr 1
    have ht : Jn.trace = J0.trace := by
      simp only [Matrix.trace, Matrix.diag, Jn, Matrix.submatrix_apply]
      exact Equiv.sum_comp e (fun i => J0 i i)
    rw [ht, hJ0]
    simp [Matrix.trace, Fintype.sum_sum_type, sub_eq_add_neg]
end Formalism.L2.Pj.DatLin
