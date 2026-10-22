-- Prove2me | solution 1 for DIGing.Push.rt_row_stochastic
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:52:42.260438+00:00
-- url     : https://prove2.me/submissions/4fd70dd5-3ca5-46ec-975f-029552c699c5

import Mathlib
import Definitions.Def_DIGing_Undir_Common
import Definitions.Def_DIGing_Push_Setting

set_option autoImplicit false

open DIGing.Push

namespace DGRAux

lemma C_nonneg {n : ℕ} (A : ℕ → Finset (Fin n × Fin n)) (C : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (h7 : Assumption7 A C) (k : ℕ) (i j : Fin n) : 0 ≤ C k i j := by
  rw [h7 k i j]
  split_ifs
  · positivity
  · exact le_rfl

lemma C_diag_pos {n : ℕ} (A : ℕ → Finset (Fin n × Fin n)) (C : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (h7 : Assumption7 A C) (k : ℕ) (i : Fin n) : 0 < C k i i := by
  rw [h7 k i i, if_pos (Or.inl rfl)]
  positivity

lemma v_succ {n : ℕ} (C : ℕ → Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (i : Fin n) :
    vSeq C (k + 1) i = ∑ j, C k i j * vSeq C k j := rfl

lemma v_pos {n : ℕ} (A : ℕ → Finset (Fin n × Fin n)) (C : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (h7 : Assumption7 A C) : ∀ k i, 0 < vSeq C k i := by
  intro k
  induction k with
  | zero => intro i; simp [vSeq]
  | succ k ih =>
    intro i
    rw [v_succ]
    have h1 : C k i i * vSeq C k i ≤ ∑ j, C k i j * vSeq C k j :=
      Finset.single_le_sum (f := fun j => C k i j * vSeq C k j)
        (fun j _ => mul_nonneg (C_nonneg A C h7 k i j) (ih j).le) (Finset.mem_univ i)
    have h2 : 0 < C k i i * vSeq C k i := mul_pos (C_diag_pos A C h7 k i) (ih i)
    linarith

lemma Rt_apply {n : ℕ} (C : ℕ → Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (i j : Fin n) :
    Rt C k i j = (vSeq C (k + 1) i)⁻¹ * C k i j * vSeq C k j := by
  unfold Rt
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

end DGRAux

open DGRAux

theorem solution {n : ℕ} (A : ℕ → Finset (Fin n × Fin n))
    (C : ℕ → Matrix (Fin n) (Fin n) ℝ) (h7 : Assumption7 A C) :
    ∀ k i, (∀ j, 0 ≤ Rt C k i j) ∧ ∑ j, Rt C k i j = 1 := by
  intro k i
  have hv := v_pos A C h7 (k + 1) i
  refine ⟨fun j => ?_, ?_⟩
  · rw [Rt_apply]
    exact mul_nonneg (mul_nonneg (inv_nonneg.2 hv.le) (C_nonneg A C h7 k i j))
      (v_pos A C h7 k j).le
  · simp_rw [Rt_apply]
    have : ∑ j, (vSeq C (k + 1) i)⁻¹ * C k i j * vSeq C k j
        = (vSeq C (k + 1) i)⁻¹ * ∑ j, C k i j * vSeq C k j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [this, ← v_succ, inv_mul_cancel₀ hv.ne']
