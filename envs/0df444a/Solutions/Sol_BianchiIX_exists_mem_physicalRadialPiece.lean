-- Prove2me | solution 1 for BianchiIX.exists_mem_physicalRadialPiece
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:05:57.580487+00:00
-- url     : https://prove2.me/submissions/03dafcb0-9b1c-4b66-8766-0f37f4ff8528

import Definitions.Def_BianchiIX_RadialFailureData
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.Order.Archimedean.Basic

noncomputable section
open BianchiIX
open Set MeasureTheory



theorem solution {d ε : ℝ} {z : SectionCoordinates} {j : ℕ}
    (hε : 0 < ε) (hz : z ∈ mainWallOpenSection d)
    (hr : mainWallRadialRadius ε z ∈ Ioo (dyadicScale d j) (2 * dyadicScale d j)) :
    ∃ k : Bool ⊕ Bool, z ∈ physicalRadialPiece d ε (k, j) := by
  by_cases hs : max (Real.exp (-z 1)) (Real.exp (-z 2)) ≤ ε * |z 0|
  · rw [mainWallRadialRadius, if_pos hs] at hr
    have hD : ![|z 0|, Real.exp (-z 1), Real.exp (-z 2)] ∈
        shearRadialDomain (dyadicScale d j) d ε :=
      ⟨Real.exp_pos _, Real.exp_pos _, hr, hs, hz.1⟩
    by_cases hs0 : 0 ≤ z 0
    · refine ⟨Sum.inl false, ![|z 0|, Real.exp (-z 1), Real.exp (-z 2)], hD, ?_⟩
      ext i
      fin_cases i <;> simp [radialPieceMap, signedShearLogCoordinates, abs_of_nonneg hs0]
    · refine ⟨Sum.inl true, ![|z 0|, Real.exp (-z 1), Real.exp (-z 2)], hD, ?_⟩
      ext i
      fin_cases i <;> simp [radialPieceMap, signedShearLogCoordinates, abs_of_neg (lt_of_not_ge hs0)]
  · rw [mainWallRadialRadius, if_neg hs] at hr
    have hgap := lt_of_not_ge hs
    by_cases hc : Real.exp (-z 2) ≤ Real.exp (-z 1)
    · rw [max_eq_left hc] at hr hgap
      have hθ : |z 0 / Real.exp (-z 1)| < 1 / ε := by
        rw [abs_div, abs_of_pos (Real.exp_pos _)]
        apply (div_lt_div_iff₀ (Real.exp_pos _) hε).mpr
        nlinarith
      have hprod : |z 0 / Real.exp (-z 1)| * Real.exp (-z 1) = |z 0| := by
        rw [abs_div, abs_of_pos (Real.exp_pos _), div_mul_cancel₀ _ (Real.exp_ne_zero _)]
      have hD : ![Real.exp (-z 1), z 0 / Real.exp (-z 1), Real.exp (-z 2)] ∈
          angularRadialDomain false (dyadicScale d j) d (1 / ε) := by
        refine ⟨hθ, Real.exp_pos _, hr, hc, ?_, ?_⟩
        · exact (le_max_left _ _).trans_lt hz.2
        · change |z 0 / Real.exp (-z 1)| * Real.exp (-z 1) < d
          rw [hprod]
          exact hz.1
      refine ⟨Sum.inr false, ![Real.exp (-z 1), z 0 / Real.exp (-z 1), Real.exp (-z 2)], hD, ?_⟩
      ext i
      fin_cases i <;> simp [radialPieceMap, orderedAngularLogCoordinates,
        scaledAngularLogCoordinates, Real.exp_ne_zero]
    · have hclt := lt_of_not_ge hc
      rw [max_eq_right hclt.le] at hr hgap
      have hθ : |-z 0 / Real.exp (-z 2)| < 1 / ε := by
        rw [abs_div, abs_neg, abs_of_pos (Real.exp_pos _)]
        apply (div_lt_div_iff₀ (Real.exp_pos _) hε).mpr
        nlinarith
      have hprod : |-z 0 / Real.exp (-z 2)| * Real.exp (-z 2) = |z 0| := by
        rw [abs_div, abs_neg, abs_of_pos (Real.exp_pos _), div_mul_cancel₀ _ (Real.exp_ne_zero _)]
      have hD : ![Real.exp (-z 2), -z 0 / Real.exp (-z 2), Real.exp (-z 1)] ∈
          angularRadialDomain true (dyadicScale d j) d (1 / ε) := by
        refine ⟨hθ, Real.exp_pos _, hr, hclt, ?_, ?_⟩
        · exact (le_max_right _ _).trans_lt hz.2
        · change |-z 0 / Real.exp (-z 2)| * Real.exp (-z 2) < d
          rw [hprod]
          exact hz.1
      refine ⟨Sum.inr true, ![Real.exp (-z 2), -z 0 / Real.exp (-z 2), Real.exp (-z 1)], hD, ?_⟩
      ext i
      fin_cases i <;> simp [radialPieceMap, orderedAngularLogCoordinates,
        scaledAngularLogCoordinates, mainWallReflection, Real.exp_ne_zero]
