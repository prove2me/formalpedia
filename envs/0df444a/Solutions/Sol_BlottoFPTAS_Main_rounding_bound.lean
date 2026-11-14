-- Prove2me | solution 1 for BlottoFPTAS.Main.rounding_bound
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-14T04:01:05.211281+00:00
-- url     : https://prove2.me/submissions/49152aa7-bf90-4001-81cd-f8ac1f542b35

import Mathlib

theorem solution {r : ℕ} (α : Fin r → ℝ) (hα : ∀ j, 0 < α j) (hsum : ∑ j, α j = 1)
    (M : ℝ) (hM : 0 < M) :
    let a : Fin r → ℕ := fun j => ⌈M * α j⌉₊
    let A : ℝ := ∑ j, (a j : ℝ)
    (∀ j, 0 < (a j : ℝ) / A) ∧ ∑ j, (a j : ℝ) / A = 1 ∧
      M ≤ A ∧ A < M + r ∧
      ∑ j, |(a j : ℝ) / A - α j| ≤
        ∑ j, |(a j : ℝ) / A - M * α j / A| + ∑ j, |M * α j / A - α j| ∧
      ∑ j, |(a j : ℝ) / A - M * α j / A| + ∑ j, |M * α j / A - α j| = 2 * (A - M) / A ∧
      2 * (A - M) / A < 2 * r / M := by
  classical
  dsimp only
  set a : Fin r → ℕ := fun j => ⌈M * α j⌉₊ with ha_def
  set A : ℝ := ∑ j, (a j : ℝ) with hA_def
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h
      simp at hsum
    · exact h
  have hMα : ∀ j, 0 < M * α j := fun j => mul_pos hM (hα j)
  have hceil_ge : ∀ j, M * α j ≤ (a j : ℝ) := fun j => Nat.le_ceil _
  have hceil_lt : ∀ j, (a j : ℝ) < M * α j + 1 :=
    fun j => Nat.ceil_lt_add_one (le_of_lt (hMα j))
  have ha_pos : ∀ j, 0 < a j := fun j => Nat.ceil_pos.mpr (hMα j)
  -- `A` is at least `M` and below `M + r`
  have hAle : M ≤ A := by
    rw [hA_def]
    calc M = ∑ j, M * α j := by rw [← Finset.mul_sum, hsum, mul_one]
      _ ≤ ∑ j, (a j : ℝ) := Finset.sum_le_sum (fun j _ => hceil_ge j)
  have hApos : 0 < A := lt_of_lt_of_le hM hAle
  have hAlt : A < M + r := by
    rw [hA_def]
    calc ∑ j, (a j : ℝ) < ∑ j, (M * α j + 1) := by
          apply Finset.sum_lt_sum
          · intro j _
            exact le_of_lt (hceil_lt j)
          · exact ⟨⟨0, hr⟩, Finset.mem_univ _, hceil_lt ⟨0, hr⟩⟩
      _ = M + r := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, mul_one]
          simp
  have hAsum : ∑ j, (a j : ℝ) / A = 1 := by
    rw [← Finset.sum_div, ← hA_def, div_self (ne_of_gt hApos)]
  -- the two error terms
  have hsum1 : ∑ j, |(a j : ℝ) / A - M * α j / A| = (A - M) / A := by
    have hterm : ∀ j, |(a j : ℝ) / A - M * α j / A| = ((a j : ℝ) - M * α j) / A := by
      intro j
      have h1 : 0 ≤ (a j : ℝ) - M * α j := by linarith [hceil_ge j]
      rw [← sub_div, abs_of_nonneg (div_nonneg h1 (le_of_lt hApos))]
    calc ∑ j, |(a j : ℝ) / A - M * α j / A| =
          ∑ j, ((a j : ℝ) - M * α j) / A := Finset.sum_congr rfl (fun j _ => hterm j)
      _ = (∑ j, ((a j : ℝ) - M * α j)) / A := (Finset.sum_div _ _ _).symm
      _ = (A - M) / A := by
          have hMsum : ∑ j, M * α j = M := by
            calc ∑ j, M * α j = M * ∑ j, α j := (Finset.mul_sum _ _ _).symm
              _ = M := by rw [hsum, mul_one]
          rw [Finset.sum_sub_distrib, ← hA_def, hMsum]
  have hsum2 : ∑ j, |M * α j / A - α j| = (A - M) / A := by
    have hterm : ∀ j, |M * α j / A - α j| = α j * ((A - M) / A) := by
      intro j
      have hMA : M / A ≤ 1 := (div_le_one hApos).mpr hAle
      have hnp : M * α j / A - α j ≤ 0 := by
        have hEq : M * α j / A - α j = α j * (M / A - 1) := by
          field_simp
        rw [hEq]
        exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hα j)) (by linarith)
      rw [abs_of_nonpos hnp]
      field_simp
      ring
    calc ∑ j, |M * α j / A - α j| = ∑ j, α j * ((A - M) / A) :=
          Finset.sum_congr rfl (fun j _ => hterm j)
      _ = (∑ j, α j) * ((A - M) / A) := (Finset.sum_mul _ _ _).symm
      _ = (A - M) / A := by rw [hsum, one_mul]
  have htri : ∑ j, |(a j : ℝ) / A - α j| ≤
      ∑ j, |(a j : ℝ) / A - M * α j / A| + ∑ j, |M * α j / A - α j| := by
    calc ∑ j, |(a j : ℝ) / A - α j| =
          ∑ j, |((a j : ℝ) / A - M * α j / A) + (M * α j / A - α j)| := by
          apply Finset.sum_congr rfl
          intro j _
          congr 1
          ring
      _ ≤ ∑ j, (|(a j : ℝ) / A - M * α j / A| + |M * α j / A - α j|) :=
          Finset.sum_le_sum (fun j _ => abs_add_le _ _)
      _ = ∑ j, |(a j : ℝ) / A - M * α j / A| + ∑ j, |M * α j / A - α j| :=
          Finset.sum_add_distrib
  have heq : ∑ j, |(a j : ℝ) / A - M * α j / A| + ∑ j, |M * α j / A - α j| =
      2 * (A - M) / A := by
    rw [hsum1, hsum2]
    ring
  have hfinal : 2 * (A - M) / A < 2 * r / M := by
    have hlt : A - M < r := by linarith
    have h1 : 2 * (A - M) / A < 2 * r / A := by
      apply div_lt_div_of_pos_right _ hApos
      linarith
    have h2 : 2 * r / A ≤ 2 * r / M := by
      apply div_le_div_of_nonneg_left _ hM hAle
      positivity
    linarith
  exact ⟨fun j => div_pos (by exact_mod_cast ha_pos j) hApos, hAsum, hAle, hAlt, htri, heq,
    hfinal⟩
