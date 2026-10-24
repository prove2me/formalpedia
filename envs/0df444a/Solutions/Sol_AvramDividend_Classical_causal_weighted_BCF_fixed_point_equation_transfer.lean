-- Prove2me | solution 1 for AvramDividend.Classical.causal_weighted_BCF_fixed_point_equation_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T08:06:46.494391+00:00
-- url     : https://prove2.me/submissions/15ad9d54-d19e-4095-bc9f-bd93f489b63c

import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- An affine BCF fixed point satisfies its unweighted Volterra equation. -/
theorem solution
    (K : ℝ → ℝ) (a β w : ℝ) (ha : 0 < a)
    (T : BoundedContinuousFunction ℝ≥0 ℝ →
      BoundedContinuousFunction ℝ≥0 ℝ)
    (f : BoundedContinuousFunction ℝ≥0 ℝ)
    (hT : ∀ (z : BoundedContinuousFunction ℝ≥0 ℝ)
      (x : ℝ) (hx : 0 ≤ x),
      T z ⟨x, hx⟩ =
        (Real.exp (-(w * x)) *
          (1 - ∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) *
            (Real.exp (w * s) *
              z ⟨max s 0, le_max_right s 0⟩) ∂volume)) / a)
    (hFixed : T f = f) :
    ∀ x : ℝ, 0 < x →
      a * (Real.exp (w * x) *
        f ⟨max x 0, le_max_right x 0⟩) + (∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) *
            (Real.exp (w * s) *
              f ⟨max s 0, le_max_right s 0⟩) ∂volume) = 1 := by
  intro x hx
  let z : ℝ≥0 := ⟨x, le_of_lt hx⟩
  let I : ℝ := (∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) *
            (Real.exp (w * s) *
              f ⟨max s 0, le_max_right s 0⟩) ∂volume)
  have hFixEval : (T f) z = f z :=
    congrArg (fun q : BoundedContinuousFunction ℝ≥0 ℝ => q z) hFixed
  have hEq : f z =
      (Real.exp (-(w * x)) * (1 - I)) / a := by
    calc
      f z = T f z := hFixEval.symm
      _ = (Real.exp (-(w * x)) * (1 - I)) / a :=
        hT f x (le_of_lt hx)
  have hz : (⟨max x 0, le_max_right x 0⟩ : ℝ≥0) = z := by
    apply Subtype.ext
    exact max_eq_left (le_of_lt hx)
  rw [hz]
  change a * (Real.exp (w * x) * f z) + I = 1
  have he : Real.exp (w * x) * Real.exp (-(w * x)) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    a * (Real.exp (w * x) * f z) + I =
        a * (Real.exp (w * x) *
          ((Real.exp (-(w * x)) * (1 - I)) / a)) + I := by rw [hEq]
    _ = (Real.exp (w * x) * Real.exp (-(w * x))) * (1 - I) + I := by
      field_simp [ne_of_gt ha]
    _ = 1 := by rw [he]; ring