-- Prove2me | solution 1 for Erdos287.five_groups_with_two_scale_distance_bands
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T09:11:36.719445+00:00
-- url     : https://prove2.me/submissions/c6fcff43-ff84-4ee8-9816-6191b225f846

import Mathlib

set_option autoImplicit false

private theorem lift_bounds (K : ℕ) (b : Fin 5 → ℕ) (L U D E : ℝ)
    (hsep : ∀ i j : Fin 5, i < j → b i + K ≤ b j)
    (hb : ∀ i j : Fin 5, i < j → ∃ s : ℝ, (s = D ∨ s = E) ∧
      L * s + K ≤ (b j : ℝ) - b i ∧ (b j : ℝ) - b i + K ≤ U * s) :
    ∃ z : Fin 5 × Fin K → ℕ, Function.Injective z ∧
      ∀ i j, i.1 ≠ j.1 → z i < z j → ∃ s : ℝ, (s = D ∨ s = E) ∧
        L * s ≤ ((z j : ℝ) - z i) ∧ (z j : ℝ) - z i ≤ U * s := by
  let z (i : Fin 5 × Fin K) := b i.1 + i.2.val
  have hlt (i j : Fin 5 × Fin K) (h : i.1 < j.1) : z i < z j := by
    have hs := hsep i.1 j.1 h
    have hi := i.2.isLt
    dsimp [z]
    omega
  refine ⟨z, ?_, ?_⟩
  · intro i j h
    have he : i.1 = j.1 := by
      rcases lt_trichotomy i.1 j.1 with hij | hij | hij
      · exact False.elim ((hlt i j hij).ne h)
      · exact hij
      · exact False.elim ((hlt j i hij).ne h.symm)
    refine Prod.ext he (Fin.ext ?_)
    dsimp [z] at h
    rw [he] at h
    omega
  · intro i j hne h
    have hij : i.1 < j.1 := by
      rcases lt_or_gt_of_ne hne with hij | hij
      · exact hij
      · exact False.elim ((hlt j i hij).asymm h)
    obtain ⟨s, hs, hlo, hhi⟩ := hb i.1 j.1 hij
    have hi : (i.2.val : ℝ) ≤ K := by exact_mod_cast i.2.isLt.le
    have hj : (j.2.val : ℝ) ≤ K := by exact_mod_cast j.2.isLt.le
    have hi₀ : (0 : ℝ) ≤ i.2.val := Nat.cast_nonneg _
    have hj₀ : (0 : ℝ) ≤ j.2.val := Nat.cast_nonneg _
    refine ⟨s, hs, ?_, ?_⟩ <;> dsimp [z] <;> push_cast <;> linarith only [hi, hj, hi₀, hj₀, hlo, hhi]

/-- Five groups realize two normalized distance bands as soon as the scales
differ by at least a factor of three halves. -/
theorem solution (K D : ℕ) (hD : 1000 * (K + 1) ≤ D)
    (R : ℝ) (hR : (3 / 2 : ℝ) ≤ R) :
    ∃ z : Fin 5 × Fin K → ℕ, Function.Injective z ∧
      ∀ i j, i.1 ≠ j.1 → z i < z j → ∃ s : ℝ, (s = D ∨ s = D * R) ∧
        if R < 5 / 2 then
          (999 / 1000 : ℝ) * s ≤ (z j : ℝ) - z i ∧
            (2668 / 1000 : ℝ) * s ≥ (z j : ℝ) - z i
        else
          (899 / 1000 : ℝ) * s ≤ (z j : ℝ) - z i ∧
            (2101 / 1000 : ℝ) * s ≥ (z j : ℝ) - z i := by
  have hdR : (1000 : ℝ) * ((K : ℝ) + 1) ≤ D := by exact_mod_cast hD
  have dp : (0 : ℝ) < D := by
    have h : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    linarith only [hdR, h]
  let E : ℝ := (D : ℝ) * R
  have hElo : (3 / 2 : ℝ) * D ≤ E := by
    simpa [E, mul_comm] using mul_le_mul_of_nonneg_left hR dp.le
  by_cases hr : R < 5 / 2
  · have hEhi : E ≤ (5 / 2 : ℝ) * D := by
      simpa [E, mul_comm] using mul_le_mul_of_nonneg_left hr.le dp.le
    let b (i : Fin 5) := i.val * D
    have hsep : ∀ i j : Fin 5, i < j → b i + K ≤ b j := by
      intro i j hij
      have h := Nat.mul_le_mul_right D (show i.val + 1 ≤ j.val from hij)
      rw [add_mul, one_mul] at h
      dsimp [b]
      omega
    have hb : ∀ i j : Fin 5, i < j → ∃ s : ℝ, (s = (D : ℝ) ∨ s = E) ∧
        (999 / 1000 : ℝ) * s + K ≤ (b j : ℝ) - b i ∧
        (b j : ℝ) - b i + K ≤ (2668 / 1000 : ℝ) * s := by
      intro i j hij
      let n := j.val - i.val
      have hn : n + i.val = j.val := Nat.sub_add_cancel hij.le
      have hn1 : 1 ≤ n := by
        have h : i.val < j.val := hij
        omega
      have hn4 : n ≤ 4 := by have h := j.isLt; omega
      have he : (b j : ℝ) - b i = (n : ℝ) * D := by
        dsimp [b]
        push_cast
        have hn' : (n : ℝ) + i.val = j.val := by exact_mod_cast hn
        rw [← hn']
        ring
      rw [he]
      interval_cases n <;> norm_num
      · exact Or.inl ⟨by linarith only [hdR], by linarith only [hdR, dp]⟩
      · exact Or.inl ⟨by linarith only [hdR, dp], by linarith only [hdR, dp]⟩
      · exact Or.inr ⟨by linarith only [hdR, dp, hEhi],
          by linarith only [hdR, dp, hElo]⟩
      · exact Or.inr ⟨by linarith only [hdR, dp, hEhi],
          by linarith only [hdR, dp, hElo]⟩
    simpa [E, hr] using (lift_bounds K b (999 / 1000) (2668 / 1000) D E hsep hb)
  · have hEhi : (5 / 2 : ℝ) * D ≤ E := by
      simpa [E, mul_comm] using mul_le_mul_of_nonneg_left (le_of_not_gt hr) dp.le
    let P : ℕ := ⌊(3 / 2 : ℝ) * E + (D : ℝ) / 2⌋₊
    have hp₁ : (P : ℝ) ≤ (3 / 2 : ℝ) * E + (D : ℝ) / 2 :=
      Nat.floor_le (by linarith only [hEhi, dp])
    have hp₂ : (3 / 2 : ℝ) * E + (D : ℝ) / 2 < (P : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hP : 2 * D + K ≤ P := by
      have h : (2 : ℝ) * D + K ≤ P := by linarith only [hp₂, hEhi, hdR, dp]
      exact_mod_cast h
    let b : Fin 5 → ℕ := ![0, D, 2 * D, P, P + D]
    have hsep : ∀ i j : Fin 5, i < j → b i + K ≤ b j := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [b] at hij ⊢ <;> omega
    have hb : ∀ i j : Fin 5, i < j → ∃ s : ℝ, (s = (D : ℝ) ∨ s = E) ∧
        (899 / 1000 : ℝ) * s + K ≤ (b j : ℝ) - b i ∧
        (b j : ℝ) - b i + K ≤ (2101 / 1000 : ℝ) * s := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> norm_num [b] at hij <;> norm_num [b]
      all_goals
        first
        | exact Or.inl ⟨by linarith only [hdR, dp], by linarith only [hdR, dp]⟩
        | exact Or.inr ⟨by linarith only [hdR, dp, hEhi, hp₂],
            by linarith only [hdR, dp, hEhi, hp₁]⟩
    simpa [E, hr] using (lift_bounds K b (899 / 1000) (2101 / 1000) D E hsep hb)

