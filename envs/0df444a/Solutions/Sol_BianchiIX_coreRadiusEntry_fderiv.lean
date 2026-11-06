-- Prove2me | solution 1 for BianchiIX.coreRadiusEntry_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T01:53:40.754745+00:00
-- url     : https://prove2.me/submissions/1d97ae72-9ebf-4e76-9dda-0eafbc7a83e6

import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Module
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_coreRadiusEntry (n : WithTop ℕ∞) {Y : CoreAngleState} (hk : 1 < Y 0) :
    ContDiffAt ℝ n coreRadiusEntry Y := by
  have hs : Y 0 ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith only [hk] : 0 < Y 0 ^ 2 - 1)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreRadiusEntry] <;> fun_prop

theorem solution {Y : CoreAngleState} (hk : 1 < Y 0) (v : CoreAngleState) :
    fderiv ℝ coreRadiusEntry Y v = ![Y 0 / Real.sqrt (Y 0 ^ 2 - 1) * v 0, v 1, 0, v 2] := by
  have hs : Y 0 ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith only [hk] : 0 < Y 0 ^ 2 - 1)
  have hd : HasDerivAt (fun s : ℝ => coreRadiusEntry (Y + s • v))
      ![Y 0 / Real.sqrt (Y 0 ^ 2 - 1) * v 0, v 1, 0, v 2] 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · have H := (((((hasDerivAt_id (0 : ℝ)).mul_const (v 0)).const_add (Y 0)).pow 2).sub_const 1).sqrt
        (by simpa using hs)
      convert! H.const_add 1 using 1
      dsimp
      ring_nf
    · simpa [coreRadiusEntry] using ((hasDerivAt_id (0 : ℝ)).mul_const (v 1)).const_add (Y 1)
    · exact hasDerivAt_const 0 1
    · simpa [coreRadiusEntry] using ((hasDerivAt_id (0 : ℝ)).mul_const (v 2)).const_add (Y 2)
  have hl : HasDerivAt (fun s : ℝ => Y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) Y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hf : HasFDerivAt coreRadiusEntry (fderiv ℝ coreRadiusEntry Y) (Y + (0 : ℝ) • v) := by
    simpa only [zero_smul, add_zero] using
      ((contDiffAt_coreRadiusEntry 1 hk).differentiableAt (by norm_num)).hasFDerivAt
  have H : HasDerivAt (fun s : ℝ => coreRadiusEntry (Y + s • v))
      (fderiv ℝ coreRadiusEntry Y v) 0 := by
    convert! hf.comp_hasDerivAt 0 hl using 1
  exact H.unique hd
