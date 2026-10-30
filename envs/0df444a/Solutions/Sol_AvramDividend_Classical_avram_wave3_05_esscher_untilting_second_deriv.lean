-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_05_esscher_untilting_second_deriv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T00:30:19.999854+00:00
-- url     : https://prove2.me/submissions/276637bb-4f83-4489-9f0b-d7e19b6ccdd0

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- Esscher untilting identifies the second derivative from the signed density. -/
theorem solution
    (V g S : ℝ → ℝ) (φ w a : ℝ)
    (hV : ∀ x : ℝ, 0 < x → HasDerivAt V (g x) x)
    (hg : ∀ x : ℝ, 0 < x →
      HasDerivAt g (Real.exp (w * x) * (S x / a)) x) :
    ∀ x : ℝ, 0 < x →
      let W : ℝ → ℝ := fun z => Real.exp (φ * z) * V z
      deriv (deriv W) x =
        2 * φ * deriv W x - φ ^ 2 * W x +
          Real.exp ((φ + w) * x) * (S x / a) := by
  intro x hx
  let W : ℝ → ℝ := fun z => Real.exp (φ * z) * V z
  have he (y : ℝ) :
      HasDerivAt (fun z : ℝ => Real.exp (φ * z))
        (φ * Real.exp (φ * y)) y := by
    simpa only [Function.comp_def, mul_one, one_mul, mul_comm] using
      ((Real.hasDerivAt_exp (φ * y)).comp y
        ((hasDerivAt_id y).const_mul φ))
  have hfirst (y : ℝ) (hy : 0 < y) :
      HasDerivAt W
        (φ * Real.exp (φ * y) * V y + Real.exp (φ * y) * g y) y :=
    (he y).mul (hV y hy)
  have hfirsteq (y : ℝ) (hy : 0 < y) :
      deriv W y =
        φ * Real.exp (φ * y) * V y + Real.exp (φ * y) * g y :=
    (hfirst y hy).deriv
  have htermV : HasDerivAt
      (fun z : ℝ => φ * (Real.exp (φ * z) * V z))
      (φ * (φ * Real.exp (φ * x) * V x + Real.exp (φ * x) * g x)) x :=
    ((he x).mul (hV x hx)).const_mul φ
  have htermG : HasDerivAt
      (fun z : ℝ => Real.exp (φ * z) * g z)
      (φ * Real.exp (φ * x) * g x +
        Real.exp (φ * x) * (Real.exp (w * x) * (S x / a))) x :=
    (he x).mul (hg x hx)
  have hsum := htermV.add htermG
  have hnear :
      (fun z : ℝ => deriv W z) =ᶠ[nhds x]
      ((fun z : ℝ => φ * (Real.exp (φ * z) * V z)) +
        (fun z : ℝ => Real.exp (φ * z) * g z)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simp only [Pi.add_apply]
    rw [hfirsteq y hy]
    ring
  have hsecond := hsum.congr_of_eventuallyEq hnear
  have hsecondeq := hsecond.deriv
  have hex : Real.exp ((φ + w) * x) =
      Real.exp (φ * x) * Real.exp (w * x) := by
    rw [add_mul, Real.exp_add]
  change deriv (deriv W) x =
    2 * φ * deriv W x - φ ^ 2 * W x +
      Real.exp ((φ + w) * x) * (S x / a)
  rw [hsecondeq, hfirsteq x hx, hex]
  dsimp [W]
  ring
