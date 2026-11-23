-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.CholeskyDecomposition.Adapted.posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:56:05.06683+00:00
-- url     : https://prove2.me/submissions/df70d0ba-f1f6-436c-941b-ac1f5796a77f

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaChol
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_Adapted_conj_apply
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_Adapted_tri
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_Adapted_conj_tri

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted CompanionTheory.D.gk.admitted.CholeskyDecomposition
open Matrix
open scoped ComplexOrder MatrixOrder
variable {n : ℕ}
variable {p : Fin n → Fin n} {b : Fin n → ℤ} {c : Fin n → ℂ}
namespace CompanionTheory.D.gk.admitted.CholeskyDecomposition
namespace Adapted
theorem _root_.solution (h : Adapted p b c) {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.BlockTriangular id)
    {a : Fin n → ℝ} (ha : ∀ i, 0 < a i) (hBa : ∀ i, B i i = a i)
    (hz : ∀ i j, b i ≠ b j → (B * (dp p 0 c * Bᴴ * dp p 0 c)) i j = 0) :
    (B * (dp p 0 c * Bᴴ * dp p 0 c)).PosSemidef := by
  set E : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => if b i = 0 ∧ b j = 0 then B i j else 0 with hE
  set d : Fin n → ℂ := fun i => if b i = 0 then 0 else ((a i * a (p i) : ℝ) : ℂ) with hd
  have key : B * (dp p 0 c * Bᴴ * dp p 0 c) = diagonal d + E * Eᴴ := by
    ext i j
    rw [Matrix.add_apply]
    by_cases hij : b i = b j
    · have hterm : ∀ k, b k ≠ b i → B i k * (dp p 0 c * Bᴴ * dp p 0 c) k j = 0 := by
        intro k hk
        rcases lt_or_gt_of_ne hk with h' | h'
        · rw [h.tri hB h', zero_mul]
        · rw [h.conj_tri hB (by omega), mul_zero]
      by_cases hi : b i = 0
      · have hj : b j = 0 := hij ▸ hi
        have hdiag : diagonal d i j = 0 := by
          by_cases e : i = j
          · subst e; simp [hd, hi]
          · simp [e]
        rw [hdiag, zero_add, Matrix.mul_apply, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk : b k = 0
        · rw [h.conj_apply, h.mid k j hk hj, h.sq, h.fix j hj, h.fix k hk]
          simp [hE, hi, hj, hk]
        · rw [hterm k (by omega)]
          simp [hE, hk]
      · obtain rfl := h.inj i j hi hij
        have hEE : (E * Eᴴ) i i = 0 := by simp [Matrix.mul_apply, hE, hi]
        rw [hEE, add_zero, Matrix.mul_apply, Finset.sum_eq_single i]
        · rw [h.conj_apply, h.sq, hBa, hBa]
          simp [hd, hi]
        · intro k _ hk
          exact hterm k fun e => hk (h.inj i k hi e.symm).symm
        · simp
    · have e : i ≠ j := fun e => hij (e ▸ rfl)
      rw [hz i j hij, diagonal_apply_ne _ e, zero_add, Matrix.mul_apply]
      symm
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hi : b i = 0
      · have hj : b j ≠ 0 := by omega
        simp [hE, hj]
      · simp [hE, hi]
  rw [key]
  refine PosSemidef.add (posSemidef_diagonal_iff.2 fun i => ?_) (posSemidef_self_mul_conjTranspose E)
  simp only [hd]
  split_ifs
  · exact le_rfl
  · exact_mod_cast (mul_pos (ha i) (ha (p i))).le
end Adapted
end CompanionTheory.D.gk.admitted.CholeskyDecomposition
