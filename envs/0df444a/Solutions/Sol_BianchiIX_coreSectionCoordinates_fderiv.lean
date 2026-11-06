-- Prove2me | solution 1 for BianchiIX.coreSectionCoordinates_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:42:44.182476+00:00
-- url     : https://prove2.me/submissions/044acff9-a086-4391-9414-6b71b7cb9ee9

import Definitions.Def_BianchiIX_Dynamics_ReferenceSectionMap
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
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
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiff_coreSectionCoordinates (n : WithTop ℕ∞) : ContDiff ℝ n coreSectionCoordinates := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreSectionCoordinates] <;> fun_prop

theorem solution (y v : ProjectiveState) :
    fderiv ℝ coreSectionCoordinates y v = coreSectionCoordinates v := by
  have hd : HasDerivAt (fun s : ℝ => coreSectionCoordinates (y + s • v)) (coreSectionCoordinates v) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [coreSectionCoordinates] using ((hasDerivAt_id (0 : ℝ)).mul_const (v 0)).const_add (y 0)
    · simpa [coreSectionCoordinates] using ((hasDerivAt_id (0 : ℝ)).mul_const (v 1)).const_add (y 1)
    · simpa [coreSectionCoordinates] using ((hasDerivAt_id (0 : ℝ)).mul_const (v 3)).const_add (y 3)
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hf : HasFDerivAt coreSectionCoordinates (fderiv ℝ coreSectionCoordinates y) (y + (0 : ℝ) • v) := by
    simpa only [zero_smul, add_zero] using
      ((contDiff_coreSectionCoordinates 1).differentiable (by norm_num) y).hasFDerivAt
  have H : HasDerivAt (fun s : ℝ => coreSectionCoordinates (y + s • v))
      (fderiv ℝ coreSectionCoordinates y v) 0 := by
    convert! hf.comp_hasDerivAt 0 hl using 1
  exact H.unique hd
