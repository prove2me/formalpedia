-- Prove2me | solution 1 for AvramDividend.Classical.causal_resolvent_exponential_renormalisation_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:27:58.169747+00:00
-- url     : https://prove2.me/submissions/eb399b93-9d7d-4729-949f-06820ddc828b

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Renormalisation by the reciprocal discount parameter preserves Laplace integrability. -/
theorem solution
    (F : ℕ → ℝ → ℝ) (θ η q : ℝ)
    (hbase : IntegrableOn
      (fun x : ℝ => Real.exp (-((η - θ) * x)) * (∑' n : ℕ, F n x))
      (Ioi (0 : ℝ)) volume) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-(η * x)) *
        ((Real.exp (θ * x) / q) * (∑' n : ℕ, F n x)))
      (Ioi (0 : ℝ)) volume := by
  have heq (x : ℝ) :
      Real.exp (-(η * x)) *
          ((Real.exp (θ * x) / q) * (∑' n : ℕ, F n x)) =
        (1 / q) * (Real.exp (-((η - θ) * x)) *
          (∑' n : ℕ, F n x)) := by
    calc
      _ = (Real.exp (-(η * x)) * Real.exp (θ * x)) *
            ((1 / q) * (∑' n : ℕ, F n x)) := by ring
      _ = Real.exp (-((η - θ) * x)) *
            ((1 / q) * (∑' n : ℕ, F n x)) := by
          rw [← Real.exp_add]
          congr 1
          ring
      _ = (1 / q) * (Real.exp (-((η - θ) * x)) *
            (∑' n : ℕ, F n x)) := by ring
  have heq_fun :
      (fun x : ℝ => Real.exp (-(η * x)) *
        ((Real.exp (θ * x) / q) * (∑' n : ℕ, F n x))) =
      (fun x : ℝ => (1 / q) *
        (Real.exp (-((η - θ) * x)) * (∑' n : ℕ, F n x))) :=
    funext heq
  rw [heq_fun]
  exact hbase.const_mul _
