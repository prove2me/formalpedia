-- Prove2me | solution 2 for DSGE.quadratic_roots_outside_unit_disk_iff
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T07:15:29.277824+00:00
-- url     : https://prove2.me/submissions/8afbae84-bd02-4dc8-81ba-7a8f79151099

import Mathlib
set_option autoImplicit false

theorem solution (T D : ℝ) (hD : 0 < D) :
    (∀ z : ℂ, z ^ 2 - (T : ℂ) * z + (D : ℂ) = 0 → 1 < ‖z‖) ↔ 1 < D ∧ |T| < 1 + D := by
  constructor
  · intro h
    have hreal : ∀ c : ℝ, c ^ 2 - T * c + D = 0 → 1 < |c| := by
      intro c hc
      have := h (c : ℂ) (by exact_mod_cast hc)
      simpa [Complex.norm_real] using this
    obtain ⟨s, hs'⟩ := IsAlgClosed.exists_eq_mul_self ((T : ℂ) ^ 2 - 4 * (D : ℂ))
    have hs : s * s = (T : ℂ) ^ 2 - 4 * (D : ℂ) := hs'.symm
    have r1 : (((T : ℂ) + s) / 2) ^ 2 - (T : ℂ) * (((T : ℂ) + s) / 2) + (D : ℂ) = 0 := by
      linear_combination (1 / 4 : ℂ) * hs
    have r2 : (((T : ℂ) - s) / 2) ^ 2 - (T : ℂ) * (((T : ℂ) - s) / 2) + (D : ℂ) = 0 := by
      linear_combination (1 / 4 : ℂ) * hs
    have hprod : (((T : ℂ) + s) / 2) * (((T : ℂ) - s) / 2) = (D : ℂ) := by
      linear_combination (-1 / 4 : ℂ) * hs
    have n1 := h _ r1
    have n2 := h _ r2
    have hDgt : 1 < D := by
      have e : ‖(((T : ℂ) + s) / 2)‖ * ‖(((T : ℂ) - s) / 2)‖ = D := by
        rw [← norm_mul, hprod, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD]
      nlinarith
    refine ⟨hDgt, ?_⟩
    have hcont : Continuous (fun x : ℝ => x ^ 2 - T * x + D) := by fun_prop
    have p1 : 0 < 1 - T + D := by
      by_contra hneg
      push_neg at hneg
      have hmem : (0 : ℝ) ∈ Set.Icc ((fun x : ℝ => x ^ 2 - T * x + D) 1)
          ((fun x : ℝ => x ^ 2 - T * x + D) 0) := by
        simp only [Set.mem_Icc]; constructor <;> nlinarith
      obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' (zero_le_one' ℝ) hcont.continuousOn hmem
      have h1 := hreal c hc0
      obtain ⟨hc1, hc2⟩ := hc
      rw [abs_of_nonneg hc1] at h1
      linarith
    have p2 : 0 < 1 + T + D := by
      by_contra hneg
      push_neg at hneg
      have hmem : (0 : ℝ) ∈ Set.Icc ((fun x : ℝ => x ^ 2 - T * x + D) (-1))
          ((fun x : ℝ => x ^ 2 - T * x + D) 0) := by
        simp only [Set.mem_Icc]; constructor <;> nlinarith
      obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc (by norm_num : (-1 : ℝ) ≤ 0)
        hcont.continuousOn hmem
      have h1 := hreal c hc0
      obtain ⟨hc1, hc2⟩ := hc
      rw [abs_of_nonpos hc2] at h1
      linarith
    rw [abs_lt]
    constructor <;> linarith
  · rintro ⟨hD1, hT⟩ z hz
    by_contra hle
    push_neg at hle
    have h1 := congrArg Complex.re hz
    have h2 := congrArg Complex.im hz
    simp [pow_two] at h1 h2
    have hn : z.re * z.re + z.im * z.im ≤ 1 := by
      have : ‖z‖ ^ 2 ≤ 1 := by
        have := norm_nonneg z
        nlinarith
      rw [Complex.sq_norm, Complex.normSq_apply] at this
      exact this
    obtain ⟨hT1, hT2⟩ := abs_lt.mp hT
    by_cases hb : z.im = 0
    · rw [hb] at h1 hn
      have ha : |z.re| ≤ 1 := by
        rw [abs_le]; constructor <;> nlinarith
      have key : 0 < (1 - |z.re|) * (D - |z.re|) + (1 + D - |T|) * |z.re| := by
        have : 0 ≤ |z.re| := abs_nonneg _
        rcases lt_or_eq_of_le ha with h | h
        · have a1 : 0 < 1 - |z.re| := by linarith
          have a2 : 0 < D - |z.re| := by linarith
          have a3 : 0 ≤ (1 + D - |T|) * |z.re| := mul_nonneg (by linarith) this
          nlinarith [mul_pos a1 a2]
        · rw [h]; nlinarith
      have e1 : T * z.re ≤ |T| * |z.re| := by
        rw [← abs_mul]; exact le_abs_self _
      have e2 : z.re * z.re = |z.re| * |z.re| := by rw [← abs_mul, abs_of_nonneg (mul_self_nonneg _)]
      nlinarith
    · have : 2 * z.re = T := by
        have : z.im * (2 * z.re - T) = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hb
        · linarith
      nlinarith
