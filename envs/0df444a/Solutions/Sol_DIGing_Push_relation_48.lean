-- Prove2me | solution 1 for DIGing.Push.relation_48
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:54:35.625308+00:00
-- url     : https://prove2.me/submissions/79abe304-8bae-414d-9e51-0abe0c80ba50

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

theorem solution {n p : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (A : ℕ → Finset (Fin n × Fin n)) (C : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (h7 : Assumption7 A C) (α : ℝ) (u x y : ℕ → DIGing.Undir.Stack n p)
    (hrun : IsPushDIGingRun f C α u x y) :
    ∀ k, x (k + 1) = DIGing.Undir.mix (Rt C k) (x k - α • hSeq C y k) ∧
      hSeq C y (k + 1) = DIGing.Undir.mix (Rt C k) (hSeq C y k) +
        (fun i => (vSeq C (k + 1) i)⁻¹ • (DIGing.Undir.gradStack f (x (k + 1)) - DIGing.Undir.gradStack f (x k)) i) := by
  obtain ⟨hu0, _, hstep⟩ := hrun
  have hvne : ∀ k i, vSeq C k i ≠ 0 := fun k i => (v_pos A C h7 k i).ne'
  have hu : ∀ k j, u k j = vSeq C k j • x k j := by
    intro k j
    cases k with
    | zero => simp [hu0, vSeq]
    | succ k =>
      rw [(hstep k).2.1]
      simp [smul_inv_smul₀ (hvne _ _)]
  have hyh : ∀ k j, y k j = vSeq C k j • hSeq C y k j := by
    intro k j
    simp [hSeq, smul_inv_smul₀ (hvne _ _)]
  intro k
  refine ⟨?_, ?_⟩
  · funext i
    rw [(hstep k).2.1]
    simp only [DIGing.Undir.mix, Pi.sub_apply, Pi.smul_apply]
    rw [(hstep k).1]
    simp only [DIGing.Undir.mix, Pi.sub_apply, Pi.smul_apply]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Rt_apply, hu k j, hyh k j]
    module
  · funext i
    have hy1 := (hstep k).2.2
    have e1 : hSeq C y (k + 1) i = (vSeq C (k + 1) i)⁻¹ • y (k + 1) i := rfl
    rw [e1, hy1]
    simp only [DIGing.Undir.mix, Pi.add_apply, Pi.sub_apply, hSeq, smul_add, smul_sub, Finset.smul_sum]
    have hsum : ∑ j, (vSeq C (k + 1) i)⁻¹ • C k i j • y k j
        = ∑ j, Rt C k i j • ((vSeq C k j)⁻¹ • y k j) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Rt_apply, smul_smul, smul_smul]
      congr 1
      have := hvne k j
      field_simp
    rw [hsum]
    simp only [DIGing.Undir.gradStack, Pi.sub_apply]
    abel
