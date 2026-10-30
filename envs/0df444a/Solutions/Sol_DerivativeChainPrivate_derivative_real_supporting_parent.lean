-- Prove2me | solution 1 for DerivativeChainPrivate.derivative_real_supporting_parent
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T03:16:12.840822+00:00
-- url     : https://prove2.me/submissions/363ed653-6f38-471b-a8b6-b364784e5ac5

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem solution (p : Polynomial ℂ) (hp : 0 < p.natDegree)
    (w : ℂ) (hw : p.derivative.eval w = 0) :
    ∃ z : ℂ, p.eval z = 0 ∧ w.re ≤ z.re := by
  have hd : p.derivative ≠ 0 := by
    intro h
    have hconst := Polynomial.derivative_eq_zero.mp h
    have hzero : p.natDegree = 0 := by simpa [hconst]
    omega
  have hwset : w ∈ p.derivative.rootSet ℂ := by
    rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval]
    exact ⟨hd, hw⟩
  have hwconv := p.rootSet_derivative_subset_convexHull_rootSet
    (Polynomial.natDegree_pos_iff_degree_pos.mp hp) hwset
  by_contra h
  push Not at h
  have hlinear : IsLinearMap ℝ (fun z : ℂ => z.re) := by
    constructor
    · intro a b; simp
    · intro a b; simp
  have hsubset : p.rootSet ℂ ⊆ {z | z.re < w.re} := by
    intro z hz
    rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval] at hz
    exact h z hz.2
  have hbad := (convexHull_min hsubset (convex_halfSpace_lt hlinear w.re)) hwconv
  exact (lt_irrefl w.re) hbad
