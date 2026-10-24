-- Prove2me | solution 1 for AvramDividend.Classical.excursion_capped_laplace_bounded_nnreal_test
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:12:50.933433+00:00
-- url     : https://prove2.me/submissions/9385ca1d-e147-420b-803d-6dc7353b29fa

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Topology

/-!
The capped Laplace test has values in [0,1]. Its NNReal-valued
continuous lift has diameter at most one, so it belongs to the
bounded-continuous test-function class used for weak convergence.
-/
theorem solution (s : ℝ) (hs : 0 ≤ s) :
    ∃ f : BoundedContinuousFunction ℝ NNReal,
      ∀ x : ℝ, (f x : ℝ) = Real.exp (-(s * max x 0)) := by
  have hcont : Continuous (fun x : ℝ => Real.exp (-(s * max x 0))) := by
    fun_prop
  have hb (x : ℝ) :
      0 < Real.exp (-(s * max x 0)) ∧
      Real.exp (-(s * max x 0)) ≤ 1 := by
    constructor
    · exact Real.exp_pos _
    have hm : 0 ≤ max x 0 := le_max_right x 0
    have hnonneg : 0 ≤ s * max x 0 := mul_nonneg hs hm
    have hneg : -(s * max x 0) ≤ 0 := neg_nonpos.mpr hnonneg
    calc
      Real.exp (-(s * max x 0)) ≤ Real.exp 0 := Real.exp_le_exp.mpr hneg
      _ = 1 := Real.exp_zero
  let g : ℝ → NNReal := fun x =>
    ⟨Real.exp (-(s * max x 0)), le_of_lt (hb x).1⟩
  have hgc : Continuous g := hcont.subtype_mk _
  have hzero (x : ℝ) : 0 ≤ (g x : ℝ) := (g x).property
  have hone (x : ℝ) : (g x : ℝ) ≤ 1 := (hb x).2
  have hdiam : ∀ x y : ℝ, dist (g x) (g y) ≤ 1 := by
    intro x y
    rw [NNReal.dist_eq]
    apply abs_le.mpr
    constructor <;> linarith [hzero x, hzero y, hone x, hone y]
  let f : BoundedContinuousFunction ℝ NNReal :=
    BoundedContinuousFunction.mkOfBound ⟨g, hgc⟩ 1 hdiam
  refine ⟨f, ?_⟩
  intro x
  change (g x : ℝ) = Real.exp (-(s * max x 0))
  rfl
