-- Prove2me | solution 1 for D1Bound5.coherent_terminal_root_norm_sq_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T22:59:27.411318+00:00
-- url     : https://prove2.me/submissions/3c77aca2-f88d-4c8f-8b54-7724e7d189c0

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_CoherentIntegralForms_Definitions
import Theorems.Thm_D1Bound5_coherent_analytic_terminal_root_sq

section
open Finset

namespace D1Bound5



/-- The exact chosen terminal root supplies both modulus-square
estimates used by the retained scalar conversion. -/
theorem _root_.solution
    (p q eta : ℂ) (hp : p ≠ 0) (hq : q ≠ 0) (heta : eta^2=p*q)
    (hPQ : 4000 < ‖p‖*‖q‖) :
    (3999/4000 : ℝ)*‖p‖*‖q‖ < ‖coherentTerminalRoot p q eta‖^2 ∧
      ‖coherentTerminalRoot p q eta‖^2 ≤ ‖p‖*‖q‖+1 := by
  have hs : (coherentTerminalRoot p q eta)^2 = p*q+1 :=
    coherent_analytic_terminal_root_sq p q eta hp hq heta
  have hnorm : ‖coherentTerminalRoot p q eta‖^2 = ‖p*q+1‖ := by
    simpa only [norm_pow] using congrArg norm hs
  have hupper : ‖p*q+1‖ ≤ ‖p‖*‖q‖+1 := by
    simpa only [norm_mul,norm_one] using norm_add_le (p*q) (1:ℂ)
  have hlower : ‖p‖*‖q‖-1 ≤ ‖p*q+1‖ := by
    have h := norm_sub_le (p*q+1) (1:ℂ)
    simp only [add_sub_cancel_right,norm_mul,norm_one] at h
    linarith
  rw [hnorm]
  exact ⟨by nlinarith only [hlower,hPQ],hupper⟩

end D1Bound5
end
