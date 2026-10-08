-- Prove2me | solution 1 for ConicQuadIPM.Complementarity.QT_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:07:26.016119+00:00
-- url     : https://prove2.me/submissions/da398721-c3f7-455d-b0ec-4865d8b8b112

import Mathlib
import Definitions.Def_ConicQuadIPM_Complementarity_Setting
open Matrix ConicQuadIPM.Complementarity
set_option maxRecDepth 4000

private lemma qsym (c : ConeKind) (d : ℕ) : (Qmat c d)ᵀ = Qmat c d := by
  cases c
  · simp [Qmat]
  · simp [Qmat]
  · ext a b
    change Qmat .rot d b a = Qmat .rot d a b
    simp only [Qmat]
    by_cases h : a = b
    · subst b; rfl
    · simp [h, Ne.symm h, and_comm, eq_comm]

private lemma tsym (c : ConeKind) (d : ℕ) : (Tmat c d)ᵀ = Tmat c d := by
  cases c
  · simp [Tmat]
  · simp [Tmat]
  · ext a b
    change Tmat .rot d b a = Tmat .rot d a b
    simp only [Tmat]
    simp [and_comm, eq_comm]

private lemma qsq (c : ConeKind) (d : ℕ) (hwf : BlockWF c d) : Qmat c d * Qmat c d = 1 := by
  cases c
  · simp [Qmat]
  · simp only [Qmat, diagonal_mul_diagonal]
    ext a b
    by_cases h : a.val = 0 <;> simp [h, diagonal_apply, one_apply]
  · have hd := hwf.2.2 rfl
    let z : Fin d := ⟨0, by omega⟩
    let o : Fin d := ⟨1, by omega⟩
    ext a b
    change (∑ j : Fin d, Qmat .rot d a j * Qmat .rot d j b) = if a = b then 1 else 0
    simp only [Qmat]
    by_cases ha : a.val < 2
    · have ha' : a = z ∨ a = o := by dsimp [z, o]; rcases (by omega : a.val = 0 ∨ a.val = 1) with h | h <;> [left; right] <;> apply Fin.ext <;> exact h
      rcases ha' with rfl | rfl
      · rw [Finset.sum_eq_single o]
        · by_cases hb : b = z <;> simp_all [z, o, Fin.ext_iff] <;> split_ifs <;> simp_all <;> omega
        · intro j hj hjo
          have : j.val ≠ 1 := by intro h; apply hjo; apply Fin.ext; exact h
          simp [z, o, this]; split_ifs <;> simp_all <;> omega
        · simp
      · rw [Finset.sum_eq_single z]
        · by_cases hb : b = o <;> simp_all [z, o, Fin.ext_iff] <;> split_ifs <;> simp_all <;> omega
        · intro j hj hjz
          have : j.val ≠ 0 := by intro h; apply hjz; apply Fin.ext; exact h
          simp [z, o, this]; split_ifs <;> simp_all <;> omega
        · simp
    · rw [Finset.sum_eq_single a]
      · simp [ha]
      · intro j hj hja; simp [ha, Ne.symm hja]
      · simp

private lemma tsq (c : ConeKind) (d : ℕ) (hwf : BlockWF c d) : Tmat c d * Tmat c d = 1 := by
  cases c
  · simp [Tmat]
  · simp [Tmat]
  · have hd := hwf.2.2 rfl
    have hs : (1 / Real.sqrt 2) ^ 2 = (1 : ℝ) / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
    let z : Fin d := ⟨0, by omega⟩
    let o : Fin d := ⟨1, by omega⟩
    ext a b
    change (∑ j : Fin d, Tmat .rot d a j * Tmat .rot d j b) = if a = b then 1 else 0
    simp only [Tmat]
    by_cases ha : a.val < 2
    · have he : ∀ j : Fin d, (if a.val < 2 ∧ j.val < 2 then (if a.val = 1 ∧ j.val = 1 then -(1 / Real.sqrt 2) else 1 / Real.sqrt 2) else if a = j then 1 else 0) =
          (if j = z then 1 / Real.sqrt 2 else 0) + (if j = o then (if a.val = 1 then -(1 / Real.sqrt 2) else 1 / Real.sqrt 2) else 0) := by
        intro j; simp [ha, z, o, Fin.ext_iff]; split_ifs <;> simp_all <;> omega
      simp_rw [he, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      simp [z, o, ha]
      split_ifs <;> simp_all [Fin.ext_iff] <;> try omega
      all_goals
        have hi : (Real.sqrt (2 : ℝ))⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
          rw [← mul_inv, ← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
        rw [hi]
        norm_num
    · rw [Finset.sum_eq_single a]
      · simp [ha]
      · intro j hj hja; simp [ha, Ne.symm hja]
      · simp

theorem solution (c : ConeKind) (d : ℕ) (hwf : BlockWF c d) :
    (Qmat c d)ᵀ = Qmat c d ∧ (Tmat c d)ᵀ = Tmat c d ∧
    (Qmat c d)ᵀ * Qmat c d = 1 ∧ (Tmat c d)ᵀ * Tmat c d = 1 ∧
    Qmat c d * Qmat c d = 1 ∧ Tmat c d * Tmat c d = 1 := by
  rw [qsym, tsym]
  exact ⟨rfl, rfl, qsq c d hwf, tsq c d hwf, qsq c d hwf, tsq c d hwf⟩

#print axioms solution
