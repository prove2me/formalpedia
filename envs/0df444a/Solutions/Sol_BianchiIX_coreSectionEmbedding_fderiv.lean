-- Prove2me | solution 1 for BianchiIX.coreSectionEmbedding_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:42:42.157333+00:00
-- url     : https://prove2.me/submissions/8bc573de-c9fb-4c91-beec-8428c271d3a4

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

private theorem BianchiIX.contDiff_coreSectionEmbedding (n : WithTop ℕ∞) : ContDiff ℝ n coreSectionEmbedding := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreSectionEmbedding] <;> fun_prop

theorem solution (z v : CoreCoordinates) :
    fderiv ℝ coreSectionEmbedding z v = ![v 0, v 1, 0, v 2] := by
  have hd : HasDerivAt (fun s : ℝ => coreSectionEmbedding (z + s • v)) ![v 0, v 1, 0, v 2] 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [coreSectionEmbedding] using ((hasDerivAt_id (0 : ℝ)).mul_const (v 0)).const_add (z 0)
    · simpa [coreSectionEmbedding] using ((hasDerivAt_id (0 : ℝ)).mul_const (v 1)).const_add (z 1)
    · exact hasDerivAt_const 0 1
    · simpa [coreSectionEmbedding] using ((hasDerivAt_id (0 : ℝ)).mul_const (v 2)).const_add (z 2)
  have hl : HasDerivAt (fun s : ℝ => z + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) z).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hf : HasFDerivAt coreSectionEmbedding (fderiv ℝ coreSectionEmbedding z) (z + (0 : ℝ) • v) := by
    simpa only [zero_smul, add_zero] using
      ((contDiff_coreSectionEmbedding 1).differentiable (by norm_num) z).hasFDerivAt
  have H : HasDerivAt (fun s : ℝ => coreSectionEmbedding (z + s • v))
      (fderiv ℝ coreSectionEmbedding z v) 0 := by
    convert! hf.comp_hasDerivAt 0 hl using 1
  exact H.unique hd
