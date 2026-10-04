-- Prove2me | solution 1 for AvramDividend.Classical.normalized_eventual_derivative_growth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-03T12:20:59.792672+00:00
-- url     : https://prove2.me/submissions/283d1fb8-a3f1-4042-ace2-66b1ba5ddbfb

import Mathlib

open Set Filter

/-
Normalized monotonicity plus a differential inequality gives an eventual
exponential lower bound on the derivative.

Assume `phi > 0`, that `g t = exp (-phi * t) * W t` is monotone on
`(0, inf)`, that `W` is strictly positive at one point `x0 > 0`, and that
`phi * W x <= deriv W x` for every `x > 0`. Set

    c = phi * exp (-phi * x0) * W x0,

which is strictly positive. Monotonicity of `g` says
`exp (-phi * x0) * W x0 <= exp (-phi * x) * W x` for `x >= x0`, and after
multiplying by the positive factor `phi * exp (phi * x)` and cancelling
`exp (-phi * x) * exp (phi * x) = 1`, this reads

    c * exp (phi * x) <= phi * W x <= deriv W x,

which is the exact conclusion shape of
`scaleDeriv_eventually_ge_exp`.

The stochastic premise (existence of a suitable `phi`) is NOT proved here.
-/
theorem solution
    (W : ℝ → ℝ) (φ x₀ : ℝ)
    (hφ : 0 < φ) (hx₀ : 0 < x₀) (hW₀ : 0 < W x₀)
    (hg : MonotoneOn (fun t : ℝ => Real.exp (-φ * t) * W t) (Ioi 0))
    (hd : ∀ x : ℝ, 0 < x → φ * W x ≤ deriv W x) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ x in atTop, c * Real.exp (φ * x) ≤ deriv W x := by
  let c : ℝ := φ * (Real.exp (-φ * x₀) * W x₀)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  refine ⟨c, hc, ?_⟩
  filter_upwards [eventually_ge_atTop x₀] with x hx
  have hxpos : 0 < x := lt_of_lt_of_le hx₀ hx
  have hm := hg (show x₀ ∈ Ioi (0 : ℝ) from hx₀)
    (show x ∈ Ioi (0 : ℝ) from hxpos) hx
  have hle :
      (φ * Real.exp (φ * x)) * (Real.exp (-φ * x₀) * W x₀) ≤
        (φ * Real.exp (φ * x)) * (Real.exp (-φ * x) * W x) :=
    mul_le_mul_of_nonneg_left hm
      (le_of_lt (mul_pos hφ (Real.exp_pos _)))
  have hcancel : Real.exp (-φ * x) * Real.exp (φ * x) = (1 : ℝ) := by
    rw [← Real.exp_add]
    have : -φ * x + φ * x = 0 := by ring
    rw [this]
    simp
  change (φ * (Real.exp (-φ * x₀) * W x₀)) * Real.exp (φ * x) ≤ deriv W x
  calc
    (φ * (Real.exp (-φ * x₀) * W x₀)) * Real.exp (φ * x) =
        (φ * Real.exp (φ * x)) * (Real.exp (-φ * x₀) * W x₀) := by ring
    _ ≤ (φ * Real.exp (φ * x)) * (Real.exp (-φ * x) * W x) := hle
    _ = φ * W x := by
      calc
        (φ * Real.exp (φ * x)) * (Real.exp (-φ * x) * W x) =
            φ * (Real.exp (-φ * x) * Real.exp (φ * x)) * W x := by ring
        _ = φ * W x := by rw [hcancel]; ring
    _ ≤ deriv W x := hd x hxpos
