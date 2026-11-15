-- Prove2me | solution 1 for DetANN.mgg_fourier_inequality
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-14T21:31:29.259252+00:00
-- url     : https://prove2.me/submissions/c339d60c-3a89-4994-85d0-883b1cce2f9f

import Mathlib
import Theorems.Thm_DetANN_mgg_cosine_inequality

open DetANN

namespace MGGBred

open Complex in
/-- `|1 + ψ(-t)| = 2 |cos(π t̃ / m)|` for the standard character `ψ` of `ℤ_m`. -/
lemma norm_one_add_char {m : ℕ} [NeZero m] (t : ZMod m) :
    ‖1 + ZMod.stdAddChar (-t)‖ = 2 * |Real.cos (Real.pi * (t.valMinAbs : ℝ) / m)| := by
  set θ : ℝ := Real.pi * (t.valMinAbs : ℝ) / m with hθ
  have ht : -t = ((-t.valMinAbs : ℤ) : ZMod m) := by
    rw [Int.cast_neg, ZMod.coe_valMinAbs]
  have hexp : exp (2 * Real.pi * I * ((-t.valMinAbs : ℤ) : ℂ) / m) =
      exp ((-θ : ℝ) * I) * exp ((-θ : ℝ) * I) := by
    rw [← exp_add]; congr 1; rw [hθ]; push_cast; ring
  have h1 : exp ((-θ : ℝ) * I) * exp ((θ : ℝ) * I) = 1 := by
    rw [← exp_add]; push_cast; ring_nf; exact exp_zero
  have key : (1 : ℂ) + exp ((-θ : ℝ) * I) * exp ((-θ : ℝ) * I) =
      exp ((-θ : ℝ) * I) * (2 * (Real.cos θ : ℂ)) := by
    rw [ofReal_cos, two_cos]
    push_cast at h1 ⊢
    linear_combination (-1 : ℂ) * h1
  rw [ht, ZMod.stdAddChar_coe, hexp, key, norm_mul, norm_exp_ofReal_mul_I, one_mul,
    show (2 * (Real.cos θ : ℂ)) = ((2 * Real.cos θ : ℝ) : ℂ) by push_cast; ring, norm_real,
    Real.norm_eq_abs, abs_mul, abs_two]

end MGGBred

open MGGBred in
theorem solution (m : ℕ) [NeZero m] (F : ZMod m × ZMod m → ℂ) (hF : F 0 = 0) :
    ‖∑ z, starRingEnd ℂ (F z) *
        (F (z.1, z.2 - 2 * z.1) * (1 + ZMod.stdAddChar (-z.1)) +
          F (z.1 - 2 * z.2, z.2) * (1 + ZMod.stdAddChar (-z.2)))‖
      ≤ 5 * Real.sqrt 2 / 2 * ∑ z, ‖F z‖ ^ 2 := by
  have hC := mgg_cosine_inequality m (fun z => ‖F z‖) (fun z => norm_nonneg _) (by simp [hF])
  refine (norm_sum_le _ _).trans (le_trans (Finset.sum_le_sum (fun z _ => ?_)) hC)
  rw [norm_mul, Complex.norm_conj]
  have hn : ‖F (z.1, z.2 - 2 * z.1) * (1 + ZMod.stdAddChar (-z.1)) +
      F (z.1 - 2 * z.2, z.2) * (1 + ZMod.stdAddChar (-z.2))‖ ≤
      ‖F (z.1, z.2 - 2 * z.1)‖ * (2 * |Real.cos (Real.pi * (z.1.valMinAbs : ℝ) / m)|) +
      ‖F (z.1 - 2 * z.2, z.2)‖ * (2 * |Real.cos (Real.pi * (z.2.valMinAbs : ℝ) / m)|) := by
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_mul, norm_mul, norm_one_add_char, norm_one_add_char]
  calc ‖F z‖ * ‖F (z.1, z.2 - 2 * z.1) * (1 + ZMod.stdAddChar (-z.1)) +
        F (z.1 - 2 * z.2, z.2) * (1 + ZMod.stdAddChar (-z.2))‖
      ≤ ‖F z‖ * (‖F (z.1, z.2 - 2 * z.1)‖ * (2 * |Real.cos (Real.pi * (z.1.valMinAbs : ℝ) / m)|) +
        ‖F (z.1 - 2 * z.2, z.2)‖ * (2 * |Real.cos (Real.pi * (z.2.valMinAbs : ℝ) / m)|)) :=
        mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    _ = _ := by ring
