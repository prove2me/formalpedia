-- Prove2me | solution 1 for DisentanglementImpossibility.householder_orthogonal_entries_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-24T21:10:01.987222+00:00
-- url     : https://prove2.me/submissions/9b585a76-7865-4ce3-a7c0-a8781f0aca23

import Mathlib
import Definitions.Def_DisentanglementImpossibility_Basic

open MeasureTheory ProbabilityTheory
namespace DisentanglementImpossibility

theorem householder_orthogonal_entries_ne_zero {d : ℕ} (hd : 1 < d) :
    (∀ α ∈ Set.Ioo (0 : ℝ) (1 / 2),
      (∑ i, householderVec d α i ^ 2 = 1) ∧
      householderMat d α ∈ Matrix.orthogonalGroup (Fin d) ℝ ∧
      (∀ i j, householderMat d α i j ≠ 0)) ∧
    Set.InjOn (householderMat d) (Set.Ioo (0 : ℝ) (1 / 2)) := by
  classical
  have hd1 : (0:ℝ) < (d:ℝ) - 1 := by
    have : (2:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hA : ∀ α, ∀ i j, householderMat d α i j =
      (if i = j then 1 else 0) - 2 * (householderVec d α i * householderVec d α j) := by
    intro α i j
    simp [householderMat, Matrix.one_apply, Matrix.vecMulVec_apply]
  have hmul : ∀ α, ∀ i, householderVec d α i * householderVec d α i = Real.sqrt α * Real.sqrt α ∨
      householderVec d α i * householderVec d α i =
        Real.sqrt ((1 - α) / ((d : ℝ) - 1)) * Real.sqrt ((1 - α) / ((d : ℝ) - 1)) := by
    intro α i
    unfold householderVec
    split_ifs <;> simp
  have hsq : ∀ α ∈ Set.Ioo (0 : ℝ) (1 / 2), ∀ i,
      householderVec d α i ^ 2 = if i.val = 0 then α else (1 - α) / ((d : ℝ) - 1) := by
    intro α hα i
    unfold householderVec
    split_ifs
    · exact Real.sq_sqrt hα.1.le
    · exact Real.sq_sqrt (div_nonneg (by linarith [hα.2]) hd1.le)
  have hpos : ∀ α ∈ Set.Ioo (0 : ℝ) (1 / 2), ∀ i, 0 < householderVec d α i := by
    intro α hα i
    unfold householderVec
    split_ifs
    · exact Real.sqrt_pos.mpr hα.1
    · exact Real.sqrt_pos.mpr (div_pos (by linarith [hα.2]) hd1)
  have hsum : ∀ α ∈ Set.Ioo (0 : ℝ) (1 / 2), ∑ i, householderVec d α i ^ 2 = 1 := by
    intro α hα
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    rw [Fin.sum_univ_succ]
    simp only [hsq α hα, Fin.val_zero, Fin.val_succ, if_pos, Nat.succ_ne_zero, if_false,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have he : (0:ℝ) < e := by
      have : 1 ≤ e := by omega
      exact_mod_cast this
    push_cast
    rw [add_sub_cancel_right]
    field_simp
    ring
  refine ⟨fun α hα => ⟨hsum α hα, ?_, ?_⟩, ?_⟩
  · rw [Matrix.mem_orthogonalGroup_iff]
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.star_apply, star_trivial, Matrix.transpose_apply, Matrix.conjTranspose_apply, hA]
    set v := householderVec d α
    have hs : ∑ x, v x ^ 2 = 1 := hsum α hα
    have hk : ∀ k, ((if i = k then (1:ℝ) else 0) - 2 * (v i * v k)) *
        ((if j = k then (1:ℝ) else 0) - 2 * (v j * v k)) =
        (if i = k then (if j = k then (1:ℝ) else 0) else 0) - 2 * v j * (if i = k then v k else 0)
          - 2 * v i * (if j = k then v k else 0) + 4 * (v i * v j) * v k ^ 2 := by
      intro k; split_ifs <;> ring
    rw [Finset.sum_congr rfl fun k _ => hk k]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, hs, Matrix.one_apply]
    split_ifs with h1 h2 h2 <;> subst_vars <;> first | ring1 | (exfalso; simp_all)
  · intro i j
    rw [hA]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, ← sq, hsq α hα]
      split_ifs
      · linarith [hα.2]
      · intro h
        have h2 : (d:ℝ) = 3 - 2 * α := by
          field_simp at h; linarith
        have h3 : 2 < d := by
          have : (2:ℝ) < d := by linarith [hα.2]
          exact_mod_cast this
        have h4 : d < 3 := by
          have : (d:ℝ) < 3 := by linarith [hα.1]
          exact_mod_cast this
        omega
    · rw [if_neg hij]
      have := mul_pos (hpos α hα i) (hpos α hα j)
      linarith
  · intro α hα β hβ h
    have := congrFun (congrFun h ⟨0, by omega⟩) ⟨0, by omega⟩
    rw [hA, hA] at this
    simp only [householderVec, if_true] at this
    rw [Real.mul_self_sqrt hα.1.le, Real.mul_self_sqrt hβ.1.le] at this
    linarith

end DisentanglementImpossibility

open DisentanglementImpossibility in
theorem solution {d : ℕ} (hd : 1 < d) :
    (∀ α ∈ Set.Ioo (0 : ℝ) (1 / 2),
      (∑ i, householderVec d α i ^ 2 = 1) ∧
      householderMat d α ∈ Matrix.orthogonalGroup (Fin d) ℝ ∧
      (∀ i j, householderMat d α i j ≠ 0)) ∧
    Set.InjOn (householderMat d) (Set.Ioo (0 : ℝ) (1 / 2)) :=
  DisentanglementImpossibility.householder_orthogonal_entries_ne_zero hd
