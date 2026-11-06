-- Prove2me | solution 1 for BianchiIX.scaled_core_interior_above
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:07:16.727049+00:00
-- url     : https://prove2.me/submissions/0b47eafd-d272-4a71-8c22-3d95849e4cdd

import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Theorems.Thm_BianchiIX_scaled_core_return_downward
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology


/-- An interior touch would immediately move below the section, contradicting the core bounds. -/
theorem solution {β : ℝ → ProjectiveState} {a : ℝ → ℝ} {k s t : ℝ}
    (hk : 6 ≤ k)
    (ha : ∀ u ∈ Icc s t, 0 < a u)
    (hβ : ∀ u ∈ Icc s t, HasDerivAt β (a u • projectiveField (β u)) u)
    (hr : ∀ u ∈ Icc s t, 99 / 100 * k ≤ coreRadius (β u 0) (β u 2))
    (hv : ∀ u ∈ Icc s t, 1 ≤ β u 2)
    (hu : ∀ u ∈ Icc s t, 0 ≤ β u 1 ∧ β u 1 ≤ (1 / 10000) / k)
    (hw : ∀ u ∈ Icc s t, 0 ≤ β u 3 ∧ β u 3 ≤ (1 / 10000) / k) :
    ∀ u ∈ Ioo s t, 1 < β u 2 := by
  intro u hst
  have hh : u ∈ Icc s t := ⟨hst.1.le, hst.2.le⟩
  apply lt_of_le_of_ne (hv u hh)
  intro heq
  have H := scaled_core_return_downward hk hst.1 (ha u hh) (hβ u hh) heq.symm
    (fun v hvs => hv v ⟨hvs.1.le, (hvs.2.trans hst.2).le⟩) (hr u hh) (hu u hh) (hw u hh)
  obtain ⟨v, hbelow, hvt⟩ := (H.2.2.2.and (Ioo_mem_nhdsGT hst.2)).exists
  have H' := hv v ⟨(hst.1.trans hvt.1).le, hvt.2.le⟩
  linarith
