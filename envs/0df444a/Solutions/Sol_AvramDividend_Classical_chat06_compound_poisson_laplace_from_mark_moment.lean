-- Prove2me | solution 1 for AvramDividend.Classical.chat06_compound_poisson_laplace_from_mark_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:59:37.506985+00:00
-- url     : https://prove2.me/submissions/9c5494a6-35bd-4c48-bbe6-858d7ae7453d

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.HasLaw
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal Nat

namespace AvramChat06


/-- The ordinary probability-generating function of a Poisson count,
valid at every real argument, including zero and negative values. -/
theorem poisson_count_pgf_general (r : ℝ≥0) (m : ℝ) :
    (∫ n : ℕ, m ^ n ∂poissonMeasure r) =
      Real.exp ((r : ℝ) * (m - 1)) := by
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  calc
    (∑' n : ℕ, Real.exp (-(r : ℝ)) *
        (r : ℝ) ^ n / n.factorial * m ^ n) =
      ∑' n : ℕ, Real.exp (-(r : ℝ)) *
        (((r : ℝ) * m) ^ n / n.factorial) := by
          congr 1
          funext n
          rw [mul_pow]
          ring
    _ = Real.exp (-(r : ℝ)) *
        ∑' n : ℕ, (((r : ℝ) * m) ^ n / n.factorial) :=
          tsum_mul_left
    _ = Real.exp (-(r : ℝ)) *
        Real.exp ((r : ℝ) * m) := by
          rw [(NormedSpace.expSeries_div_hasSum_exp
            ((r : ℝ) * m)).tsum_eq, exp_eq_exp_ℝ]
    _ = Real.exp ((r : ℝ) * (m - 1)) := by
          rw [← Real.exp_add]
          congr 1
          ring


/-- Exact marked compound-Poisson Laplace transform.
The single remaining probabilistic premise is the conditional
marked-sum moment factorisation at the random Poisson count. -/
theorem compound_poisson_laplace_from_mark_moment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (N : Ω → ℕ) (X : Ω → ℝ)
    (t : ℝ≥0) (θ m : ℝ)
    (hN : HasLaw N (poissonMeasure t) P)
    (hmark : (∫ ω, Real.exp (θ * (X ω - (t : ℝ))) ∂P) =
      ∫ ω, m ^ (N ω) ∂P) :
    (∫ ω, Real.exp (θ * X ω) ∂P) =
      Real.exp ((t : ℝ) * (θ + m - 1)) := by
  have hcount :
      (∫ ω, m ^ (N ω) ∂P) =
        Real.exp ((t : ℝ) * (m - 1)) := by
    have hi := hN.integral_comp
      (f := fun n : ℕ => m ^ n)
      (by fun_prop : AEStronglyMeasurable
        (fun n : ℕ => m ^ n) (poissonMeasure t))
    change (∫ ω, m ^ (N ω) ∂P) =
      (∫ n : ℕ, m ^ n ∂poissonMeasure t) at hi
    rw [hi]
    exact poisson_count_pgf_general t m
  have hfac (ω : Ω) :
      Real.exp (θ * X ω) =
        Real.exp (θ * (t : ℝ)) *
          Real.exp (θ * (X ω - (t : ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    (∫ ω, Real.exp (θ * X ω) ∂P) =
      Real.exp (θ * (t : ℝ)) *
        (∫ ω, Real.exp (θ * (X ω - (t : ℝ))) ∂P) := by
          simp_rw [hfac]
          rw [integral_const_mul]
    _ = Real.exp (θ * (t : ℝ)) *
      (∫ ω, m ^ (N ω) ∂P) := by rw [hmark]
    _ = Real.exp (θ * (t : ℝ)) *
      Real.exp ((t : ℝ) * (m - 1)) := by rw [hcount]
    _ = Real.exp ((t : ℝ) * (θ + m - 1)) := by
      rw [← Real.exp_add]
      congr 1
      ring

end AvramChat06

open AvramChat06

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (N : Ω → ℕ) (X : Ω → ℝ)
    (t : ℝ≥0) (θ m : ℝ)
    (hN : HasLaw N (poissonMeasure t) P)
    (hmark : (∫ ω, Real.exp (θ * (X ω - (t : ℝ))) ∂P) =
      ∫ ω, m ^ (N ω) ∂P) :
    (∫ ω, Real.exp (θ * X ω) ∂P) =
      Real.exp ((t : ℝ) * (θ + m - 1)) := by
  exact compound_poisson_laplace_from_mark_moment N X t θ m hN hmark
