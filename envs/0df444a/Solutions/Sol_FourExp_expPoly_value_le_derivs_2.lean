-- Prove2me | solution 2 for FourExp.expPoly_value_le_derivs
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T04:11:05.243557+00:00
-- url     : https://prove2.me/submissions/6992a8c1-e398-4e40-b0ec-f2ddba6caa7e

import Mathlib
import Theorems.Thm_Transcendence_expPoly_iteratedDeriv_le

/-!
# The value of an exponential polynomial from its first derivatives at `0`

Write `N = ∑ⱼ qⱼ` and `f(z) = ∑ⱼ Pⱼ(z) e^{wⱼ z}`. If `N = 0`, every `Pⱼ` is zero and so is `f`.
Otherwise `0 ≤ D` (from `s = 0`), and `Transcendence.expPoly_iteratedDeriv_le` at `c = 0` gives
`‖f⁽ⁿ⁾(0)‖ ≤ D (W + 1)^{n + N}` for every `n`. The Taylor series of the entire function `f` at `0`
then gives `‖f(u)‖ ≤ ∑ₙ Rⁿ/n! · D (W + 1)^{n + N} ≤ D (W + 1)^N e^{(W + 1) R}`, which is at most
`N (W + 1)^{N + 1} e^{R (W + 1)} D`. The injectivity of `w` is not needed.
-/

open Finset in
theorem solution
    {l : ℕ} (q : Fin l → ℕ) (w : Fin l → ℂ) (hw : Function.Injective w)
    (P : Fin l → Polynomial ℂ) (hP : ∀ j, P j = 0 ∨ (P j).natDegree < q j)
    (W R D : ℝ) (hW0 : 0 ≤ W) (hW : ∀ j, ‖w j‖ ≤ W) (hR : 0 ≤ R)
    (hD : ∀ s : ℕ, s < ∑ j, q j →
      ‖iteratedDeriv s (fun z : ℂ => ∑ j, (P j).eval z * Complex.exp (w j * z)) 0‖ ≤ D)
    (u : ℂ) (hu : ‖u‖ ≤ R) :
    ‖∑ j, (P j).eval u * Complex.exp (w j * u)‖
      ≤ ((∑ j, q j : ℕ) : ℝ) * (W + 1) ^ ((∑ j, q j) + 1) * Real.exp (R * (W + 1)) * D := by
  have _ := hw  -- the injectivity of `w` is not needed
  set N := ∑ j, q j with hN
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · have hs0 : ∑ j, q j = 0 := hN0
    have hP0 : ∀ j, P j = 0 := fun j => (hP j).resolve_right (by
      rw [Finset.sum_eq_zero_iff.1 hs0 j (Finset.mem_univ j)]; exact Nat.not_lt_zero _)
    simp [hP0, hN0]
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0 hNpos)
  have hbd := Transcendence.expPoly_iteratedDeriv_le w W hW0 hW 0 N q P hP hN.symm D hD0 hD
  -- Taylor at `0`: `‖f(u)‖ ≤ ∑ₙ ‖u‖ⁿ/n! · D (W + 1)^(n + N) ≤ D (W + 1)^N e^{(W + 1) R}`
  have hT := Complex.hasSum_taylorSeries_of_entire (c := 0) (z := u)
    (show Differentiable ℂ (fun z : ℂ => ∑ j, (P j).eval z * Complex.exp (w j * z)) by fun_prop)
  have hle : ‖∑ j, (P j).eval u * Complex.exp (w j * u)‖
      ≤ D * (W + 1) ^ N * Real.exp ((W + 1) * R) := by
    refine le_of_tendsto' hT.tendsto_sum_nat.norm fun K => (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ n ∈ range K, D * (W + 1) ^ N * (((W + 1) * R) ^ n / (n.factorial : ℝ)) := by
          refine Finset.sum_le_sum fun n _ => ?_
          rw [sub_zero, norm_smul, norm_smul, norm_inv, norm_pow, Complex.norm_natCast]
          calc _ ≤ (n.factorial : ℝ)⁻¹ * (R ^ n * (D * (W + 1) ^ (n + N))) := by
                gcongr; exact hbd n
            _ = _ := by rw [mul_pow, pow_add]; ring
      _ = D * (W + 1) ^ N * ∑ n ∈ range K, ((W + 1) * R) ^ n / (n.factorial : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ _ := by gcongr; exact Real.sum_le_exp_of_nonneg (by positivity) K
  calc _ ≤ D * (W + 1) ^ N * Real.exp ((W + 1) * R) := hle
    _ ≤ D * ((N : ℝ) * (W + 1) ^ (N + 1)) * Real.exp (R * (W + 1)) := by
        rw [mul_comm (W + 1) R]
        gcongr
        calc (W + 1) ^ N ≤ (W + 1) ^ (N + 1) := pow_le_pow_right₀ (by linarith) (by omega)
          _ ≤ _ := le_mul_of_one_le_left (by positivity) (by exact_mod_cast hNpos)
    _ = _ := by ring
