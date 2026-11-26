-- Prove2me | solution 1 for Erdos287.count_and_unit_gaps_lower_bound_from_first_denominator
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T09:52:33.901837+00:00
-- url     : https://prove2.me/submissions/1b393f32-16e8-44c1-9a1f-710a219eff70

import Mathlib

open Finset MeasureTheory

set_option autoImplicit false

/-- Compressing the denominators to the left gives an exponential lower
bound on their count. For gaps at most two it gives a unit-gap lower bound. -/
theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ) (hmin : 1 < f 0)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1) :
    (Real.exp 1 - 1) * ((f 0 : ℝ) - 1) ≤ (k : ℝ) ∧
    ((∀ i, i + 1 < k → f (i + 1) - f i ≤ 2) →
      (2 * Real.exp 1 - 1) * f 0 - f (k - 1) - 2 * Real.exp 1 ≤
        (((Finset.range (k - 1)).filter (fun i => f (i + 1) - f i = 1)).card : ℝ)) := by
  let z := f 0 - 1
  have hz : 0 < z := by dsimp [z]; omega
  have hzR : (0 : ℝ) < z := by exact_mod_cast hz
  have hzshift : z + 1 = f 0 := by dsimp [z]; omega
  have hleft (i : ℕ) (hi : i < k) : z + i + 1 ≤ f i := by
    induction i with
    | zero => simp only [Nat.add_zero, hzshift, le_refl]
    | succ i ih =>
      have h := ih (by omega)
      have hs := hmono i (i + 1) (by omega) hi
      omega
  have hsumR : ∑ i ∈ range k, (1 : ℝ) / f i = 1 := by
    simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using
      congrArg (fun x : ℚ => (x : ℝ)) hsum
  have himage : (range k).image (fun i => z + i) = Ico z (z + k) := by
    ext j
    simp only [mem_image, mem_range, mem_Ico]
    constructor
    · rintro ⟨i, hi, rfl⟩
      omega
    · rintro ⟨hlo, hhi⟩
      exact ⟨j - z, by omega, by omega⟩
  have hanti : AntitoneOn (fun x : ℝ => 1 / x) (Set.Icc (z : ℝ) ((z + k : ℕ) : ℝ)) := by
    intro x hx y _ hxy
    exact one_div_le_one_div_of_le (hzR.trans_le hx.1) hxy
  have htop : (0 : ℝ) < (z + k : ℕ) := by positivity
  have hlog : (1 : ℝ) ≤ Real.log (((z + k : ℕ) : ℝ) / z) := calc
    1 = ∑ i ∈ range k, (1 : ℝ) / f i := hsumR.symm
    _ ≤ ∑ i ∈ range k, (1 : ℝ) / ((z + i + 1 : ℕ) : ℝ) := by
      apply sum_le_sum
      intro i hi
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hleft i (mem_range.mp hi))
    _ = ∑ j ∈ Ico z (z + k), (1 : ℝ) / ((j + 1 : ℕ) : ℝ) := by
      rw [← himage, sum_image (fun _ _ _ _ h => Nat.add_left_cancel h)]
    _ ≤ ∫ t in (z : ℝ)..((z + k : ℕ) : ℝ), 1 / t :=
      AntitoneOn.sum_le_integral_Ico (Nat.le_add_right _ _) hanti
    _ = _ := integral_one_div_of_pos hzR htop
  have hbound : Real.exp 1 * (z : ℝ) ≤ ((z + k : ℕ) : ℝ) := by
    apply (le_div_iff₀ hzR).mp
    calc
      Real.exp 1 ≤ Real.exp (Real.log (((z + k : ℕ) : ℝ) / z)) := Real.exp_le_exp.mpr hlog
      _ = _ := Real.exp_log (div_pos htop hzR)
  have hzcast : (z : ℝ) = (f 0 : ℝ) - 1 := by
    dsimp [z]
    rw [Nat.cast_sub (show 1 ≤ f 0 by omega), Nat.cast_one]
  have hnum : (Real.exp 1 - 1) * ((f 0 : ℝ) - 1) ≤ (k : ℝ) := by
    push_cast at hbound
    rw [hzcast] at hbound
    nlinarith only [hbound]
  refine ⟨hnum, ?_⟩
  intro hgap
  let U := (range (k - 1)).filter (fun i => f (i + 1) - f i = 1)
  have hcount : (∑ i ∈ range (k - 1), if f (i + 1) - f i = 1 then (1 : ℝ) else 0) =
      (U.card : ℝ) := by
    rw [← sum_filter]
    simp [U]
  have htel : (∑ i ∈ range (k - 1), ((f (i + 1) - f i : ℕ) : ℝ)) =
      (f (k - 1) : ℝ) - f 0 := calc
    _ = ∑ i ∈ range (k - 1), ((f (i + 1) : ℝ) - f i) := by
      apply sum_congr rfl
      intro i hi
      have h := mem_range.mp hi
      exact Nat.cast_sub (hmono i (i + 1) (by omega) (by omega)).le
    _ = _ := sum_range_sub (fun i => (f i : ℝ)) (k - 1)
  have hs : (∑ i ∈ range (k - 1), (((f (i + 1) - f i : ℕ) : ℝ) +
      (if f (i + 1) - f i = 1 then (1 : ℝ) else 0))) =
        ∑ _i ∈ range (k - 1), (2 : ℝ) := by
    apply sum_congr rfl
    intro i hi
    have h := mem_range.mp hi
    have h₁ := hmono i (i + 1) (by omega) (by omega)
    have h₂ := hgap i (by omega)
    rcases (show f (i + 1) - f i = 1 ∨ f (i + 1) - f i = 2 by omega) with h | h
    · norm_num [h]
    · norm_num [h]
  rw [sum_add_distrib, htel, hcount] at hs
  simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_one] at hs
  nlinarith only [hnum, hs]

