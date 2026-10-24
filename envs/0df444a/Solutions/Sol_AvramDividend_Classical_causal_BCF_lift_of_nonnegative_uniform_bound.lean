-- Prove2me | solution 1 for AvramDividend.Classical.causal_BCF_lift_of_nonnegative_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T07:48:51.912299+00:00
-- url     : https://prove2.me/submissions/d4bba22a-b690-4637-9bed-44e631087dbd

import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.UniformSpace.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set
open scoped NNReal

/-- A continuous uniformly bounded function on nonnegative time is a BCF. -/
theorem solution
    (F : ℝ → ℝ) (M : ℝ)
    (hContinuous : ContinuousOn F (Ici (0 : ℝ)))
    (hBound : ∀ x : ℝ, 0 ≤ x → |F x| ≤ M) :
    ∃ f : BoundedContinuousFunction ℝ≥0 ℝ,
      ∀ x : ℝ≥0, f x = F (x : ℝ) := by
  have hc : Continuous (fun x : ℝ≥0 => F (x : ℝ)) := by
    simpa only [Function.comp_def] using
      hContinuous.comp_continuous NNReal.continuous_coe
        (by intro x; exact x.property)
  let q : C(ℝ≥0, ℝ) := ⟨(fun x => F (x : ℝ)), hc⟩
  have hdiam : ∀ x y : ℝ≥0, dist (q x) (q y) ≤ 2 * M := by
    intro x y
    change dist (F (x : ℝ)) (F (y : ℝ)) ≤ 2 * M
    rw [Real.dist_eq]
    calc
      |F (x : ℝ) - F (y : ℝ)| ≤
          |F (x : ℝ)| + |F (y : ℝ)| := by
            simpa only [sub_zero, zero_sub, abs_neg] using
              (abs_sub_le (F (x : ℝ)) 0 (F (y : ℝ)))
      _ ≤ M + M := add_le_add (hBound _ x.property) (hBound _ y.property)
      _ = 2 * M := by ring
  refine ⟨BoundedContinuousFunction.mkOfBound q (2 * M) hdiam, ?_⟩
  intro x
  rfl