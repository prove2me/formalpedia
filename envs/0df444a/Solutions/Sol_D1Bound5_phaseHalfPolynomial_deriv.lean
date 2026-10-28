-- Prove2me | solution 1 for D1Bound5.phaseHalfPolynomial_deriv
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:54:39.430885+00:00
-- url     : https://prove2.me/submissions/b925a9d7-046b-4587-bb9b-74ace72abe5a

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_CoupledPhaseBounds_Definitions

section
namespace D1Bound5




theorem _root_.solution (q x : ℝ) :
    HasDerivAt (phaseHalfPolynomial q) (-(4-x^2)*phaseCritical q x) x := by
  have hsq : HasDerivAt (fun y : ℝ => y^2) (2*x) x := by
    simpa using! (hasDerivAt_id x).pow 2
  have hbase : HasDerivAt (fun y : ℝ => 4-y^2) (-2*x) x := by
    simpa using! (hasDerivAt_const x (4 : ℝ)).sub hsq
  have h₁ : HasDerivAt (fun y : ℝ => (4-y^2)^2)
      (2*(4-x^2)*(-2*x)) x := by
    simpa using! hbase.pow 2
  have h₂ : HasDerivAt (fun y : ℝ => 1+(1/q)^2+y/q) (1/q) x := by
    exact ((hasDerivAt_id x).div_const q).const_add (1+(1/q)^2)
  have h : HasDerivAt (phaseHalfPolynomial q)
      ((2*(4-x^2)*(-2*x))*(1+(1/q)^2+x/q)+(4-x^2)^2*(1/q)) x :=
    h₁.mul h₂
  have heq : (2*(4-x^2)*(-2*x))*(1+(1/q)^2+x/q)+(4-x^2)^2*(1/q) =
      -(4-x^2)*phaseCritical q x := by
    unfold phaseCritical
    ring
  rw [heq] at h
  exact h











end D1Bound5
end
