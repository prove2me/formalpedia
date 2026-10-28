-- Prove2me | solution 1 for D1Bound5.coherent_elementary_norm_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:45:24.668218+00:00
-- url     : https://prove2.me/submissions/e5751249-0733-4ffb-aaa1-cd75db95b11d

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
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_CoherentThreeSimultaneous_Definitions

section
open Finset

namespace D1Bound5

/-- Elementary symmetric norm bounds for four ordered anchors. -/
theorem _root_.solution
    (a : Fin 4 → ℂ)
    (h01 : ‖a 0‖ ≤ ‖a 1‖) (h12 : ‖a 1‖ ≤ ‖a 2‖) (h23 : ‖a 2‖ ≤ ‖a 3‖) :
    ‖coherentElementary2 a‖ ≤ 6 * ‖a 2‖ * ‖a 3‖ ∧
    ‖coherentElementary3 a‖ ≤ 4 * ‖a 1‖ * ‖a 2‖ * ‖a 3‖ ∧
    ‖coherentElementary4 a‖ = ‖a 0‖ * ‖a 1‖ * ‖a 2‖ * ‖a 3‖ := by
  let v2 : Fin 6 → ℂ := ![a 0*a 1, a 0*a 2, a 0*a 3,
    a 1*a 2, a 1*a 3, a 2*a 3]
  let v3 : Fin 4 → ℂ := ![a 0*a 1*a 2, a 0*a 1*a 3,
    a 0*a 2*a 3, a 1*a 2*a 3]
  have he2 : coherentElementary2 a = ∑ i, v2 i := by
    simp [coherentElementary2, v2, Fin.sum_univ_succ]
    ring
  have he3 : coherentElementary3 a = ∑ i, v3 i := by
    simp [coherentElementary3, v3, Fin.sum_univ_succ]
    ring
  have hv2 (i : Fin 6) : ‖v2 i‖ ≤ ‖a 2‖ * ‖a 3‖ := by
    fin_cases i <;> norm_num [v2, norm_mul]
    all_goals gcongr <;> linarith
  have hv3 (i : Fin 4) : ‖v3 i‖ ≤ ‖a 1‖ * ‖a 2‖ * ‖a 3‖ := by
    fin_cases i <;> norm_num [v3, norm_mul]
    all_goals gcongr <;> linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [he2]
    calc
      ‖∑ i, v2 i‖ ≤ ∑ i, ‖v2 i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin 6, ‖a 2‖ * ‖a 3‖ := Finset.sum_le_sum (fun i _ => hv2 i)
      _ = _ := by simp; ring
  · rw [he3]
    calc
      ‖∑ i, v3 i‖ ≤ ∑ i, ‖v3 i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin 4, ‖a 1‖ * ‖a 2‖ * ‖a 3‖ := Finset.sum_le_sum (fun i _ => hv3 i)
      _ = _ := by simp; ring
  · simp [coherentElementary4, norm_mul]













end D1Bound5
end
