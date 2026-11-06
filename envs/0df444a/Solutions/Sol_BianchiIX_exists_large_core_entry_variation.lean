-- Prove2me | solution 1 for BianchiIX.exists_large_core_entry_variation
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:06:27.589347+00:00
-- url     : https://prove2.me/submissions/918bddc7-fed2-441d-834b-3413bb39d3a1

import Definitions.Def_BianchiIX_Analysis_CoreGrowthBudget
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreWeightedVariation
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Theorems.Thm_BianchiIX_coreRadiusEntry_variation_norm
import Theorems.Thm_BianchiIX_exists_large_core_projected_growth
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
open Set


/-- The initial directional size controls the projected variation throughout the core. -/
theorem solution {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) :
    ∃ T > 0,
      IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Y) 0 t 2 = 1} T ∧
      (∀ t ∈ Icc 0 T, coreRegion (Y 0) (projectiveOriginalFlow (coreRadiusEntry Y) 0 t)) ∧
      ∀ t ∈ Icc 0 T, ∀ v : CoreAngleState,
        ‖scaleCoreVariation (Y 0) (coreProjectedFlowVariation (coreRadiusEntry Y) 0 t
          (fderiv ℝ coreRadiusEntry Y v))‖ ≤
          (2 * coreVariationBound) * (|v 0| + Y 0 * |v 1| + |v 2|) := by
  obtain ⟨T, hT, hfirst, hcore, hvar⟩ := exists_large_core_projected_growth hk hu hw
  refine ⟨T, hT, hfirst, fun t ht => (hcore t ht).2, ?_⟩
  intro t ht v
  have H := hvar t ht (fderiv ℝ coreRadiusEntry Y v)
  apply H.trans
  have hK : 0 ≤ coreVariationBound := (Real.exp_pos _).le
  have H' := mul_le_mul_of_nonneg_right (coreRadiusEntry_variation_norm hk hu hw v) hK
  convert! H' using 1
  ring
