-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.S4.lenCoker_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:17:50.608869+00:00
-- url     : https://prove2.me/submissions/cd2f2e4e-40b0-42c0-80f1-1dd29b92d280

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_S4_exists_topMinor_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.S4
variable {R : Type*} [CommRing R]
namespace Formalism.L2.FormalSeriesBounds.S4
theorem _root_.solution (v : AddValuation R (WithTop ℝ)) (hv : ∀ x, 0 ≤ v x) {n p h : ℕ}
    (S : Matrix (Fin n) (Fin p) R) (W : Matrix (Fin p) (Fin n) R) (hSW : S * W = 1)
    (α : Matrix (Fin p) (Fin h) R) : lenCoker v (S * α) ≤ lenCoker v α := by
  unfold lenCoker
  refine Finset.le_inf fun g _ => ?_
  change (Finset.univ.inf fun g' : Fin n → Fin h => v ((S * α).submatrix id g').det) ≤ _
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin p) (Fin p) R, Q = 1 - W * S := ⟨_, rfl⟩
  have hSQ : S * Q = 0 := by
    rw [hQ, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hSW, Matrix.one_mul, sub_self]
  have hQW : Q * W = 0 := by
    rw [hQ, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hSW, Matrix.mul_one, sub_self]
  have hWS : W * S * (W * S) = W * S := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc S, hSW, Matrix.one_mul]
  have hQQ : Q * Q + W * S = 1 := by
    rw [hQ, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hWS]
    abel
  let M := α.submatrix id g
  let Z' : Matrix (Fin n ⊕ Fin p) (Fin p ⊕ Fin n) R := Matrix.fromBlocks S 0 Q W
  let Zi : Matrix (Fin p ⊕ Fin n) (Fin n ⊕ Fin p) R := Matrix.fromBlocks W Q 0 S
  let Dm : Matrix (Fin p ⊕ Fin n) (Fin p ⊕ Fin n) R := Matrix.fromBlocks M 0 0 1
  let er : Fin n ⊕ Fin p ≃ Fin (n + p) := finSumFinEquiv
  let ec : Fin p ⊕ Fin n ≃ Fin (n + p) := (Equiv.sumComm (Fin p) (Fin n)).trans finSumFinEquiv
  have hZ : Z' * Zi = 1 := by
    simp only [Z', Zi, Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
    rw [hSW, hSQ, hQW, hQQ, Matrix.fromBlocks_one]
  have hZZ : Matrix.reindex er ec Z' * Matrix.reindex ec er Zi = 1 := by
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mul_equiv, hZ, Matrix.submatrix_one_equiv]
  have hv0 : v (Matrix.reindex er ec Z').det = 0 := by
    have h2 := congrArg v (congrArg Matrix.det hZZ)
    rw [Matrix.det_mul, Matrix.det_one, v.map_mul, v.map_one] at h2
    refine le_antisymm ?_ (hv _)
    calc v (Matrix.reindex er ec Z').det
        ≤ v (Matrix.reindex er ec Z').det + v (Matrix.reindex ec er Zi).det := le_add_of_nonneg_right (hv _)
      _ = 0 := h2
  let Y := Matrix.reindex er ec (Z' * Dm)
  have hdetY : Y.det = (Matrix.reindex er ec Z').det * M.det := by
    simp only [Y, Matrix.reindex_apply]
    rw [← Matrix.submatrix_mul_equiv Z' Dm er.symm ec.symm ec.symm, Matrix.det_mul,
      Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
  have hvY : v Y.det = v M.det := by
    rw [hdetY, v.map_mul, hv0, zero_add]
  obtain ⟨f, -, hf⟩ := exists_topMinor_le v hv n p Y
  refine le_trans ?_ (hvY ▸ hf)
  by_cases hz : ∃ b c, ec.symm (f b) = Sum.inr c
  · obtain ⟨b, c, hb⟩ := hz
    have h0 : (Y.submatrix (Fin.castAdd p) f).det = 0 := by
      refine Matrix.det_eq_zero_of_column_eq_zero b fun i => ?_
      simp [Y, Z', Dm, er, Matrix.reindex_apply, hb, Matrix.mul_apply, Fintype.sum_sum_type]
    rw [h0, AddValuation.map_zero]
    exact le_top
  · push_neg at hz
    have hx : ∀ b, ∃ x, ec.symm (f b) = Sum.inl x := by
      intro b
      rcases hfb : ec.symm (f b) with x | c
      · exact ⟨x, rfl⟩
      · exact absurd hfb (hz b c)
    choose x hx using hx
    have heq : Y.submatrix (Fin.castAdd p) f = (S * α).submatrix id (g ∘ x) := by
      ext i b
      simp [Y, Z', Dm, M, er, Matrix.reindex_apply, hx b, Matrix.mul_apply, Fintype.sum_sum_type]
    rw [heq]
    exact Finset.inf_le (Finset.mem_univ _)
end Formalism.L2.FormalSeriesBounds.S4
