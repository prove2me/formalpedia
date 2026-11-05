-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_main_public_discount_clock_grid_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:12:50.6193+00:00
-- url     : https://prove2.me/submissions/a33c777b-c408-4655-9808-2f4ac48568c1

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped BigOperators NNReal

/-- The exact discrete discount-product term is a time integral against
right-endpoint sampled values; it does not move a dividend endpoint atom. -/
theorem solution
    (n : ℕ) (u : ℕ → ℝ≥0) (post : ℕ → ℝ) (q : ℝ) :
    (∑ i ∈ Finset.range n,
      (Real.exp (-(q * (u (i + 1) : ℝ))) -
        Real.exp (-(q * (u i : ℝ)))) * post (i + 1)) =
    ∑ i ∈ Finset.range n,
      (∫ t in (u i : ℝ)..(u (i + 1) : ℝ),
        -(q * Real.exp (-(q * t)))) * post (i + 1) := by
  let f : ℝ → ℝ := fun t => Real.exp (-(q * t))
  have hf (t : ℝ) :
      HasDerivAt f (-(q * Real.exp (-(q * t)))) t := by
    have hq : HasDerivAt (fun s : ℝ => q * s) q t := by
      simpa using (hasDerivAt_id t).const_mul q
    have hlin : HasDerivAt (fun s : ℝ => -(q * s)) (-q) t :=
      hq.neg
    have hcomp : HasDerivAt f (Real.exp (-(q * t)) * (-q)) t := by
      simpa [f, Function.comp_def] using
        (Real.hasDerivAt_exp (-(q * t))).comp t hlin
    have hm : Real.exp (-(q * t)) * (-q) =
        -(q * Real.exp (-(q * t))) := by ring
    rw [← hm]
    exact hcomp
  have hderiv (t : ℝ) :
      deriv f t = -(q * Real.exp (-(q * t))) := (hf t).deriv
  have hc : Continuous (fun t : ℝ => -(q * Real.exp (-(q * t)))) := by
    fun_prop
  have hcell (a b : ℝ) :
      Real.exp (-(q * b)) - Real.exp (-(q * a)) =
        ∫ t in a..b, -(q * Real.exp (-(q * t))) := by
    have hInt : IntervalIntegrable (deriv f) volume a b := by
      have h1 : IntervalIntegrable
          (fun t : ℝ => -(q * Real.exp (-(q * t)))) volume a b :=
        hc.intervalIntegrable a b
      have hfun : deriv f = (fun t : ℝ => -(q * Real.exp (-(q * t)))) := by
        funext t
        exact hderiv t
      rw [hfun]
      exact h1
    have hFTC := intervalIntegral.integral_deriv_eq_sub
      (a := a) (b := b) (f := f)
      (fun t _ => (hf t).differentiableAt) hInt
    simpa only [f, hderiv] using hFTC.symm
  apply Finset.sum_congr rfl
  intro i hi
  rw [hcell (u i : ℝ) (u (i + 1) : ℝ)]
