-- Prove2me | solution 1 for BianchiIX.exists_compact_core_return_two_germ
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T03:35:38.877673+00:00
-- url     : https://prove2.me/submissions/46b9cb2f-7b6d-4fde-a010-1771bc1baad3

import Definitions.Def_BianchiIX_Dynamics_ReferenceReturn
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Theorems.Thm_BianchiIX_coreRadiusReturn_reference_regular
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Tactic.NormNum
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
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology


/-- One common wall neighborhood and one bound for the first two derivatives on the compact core. -/
theorem solution :
    ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (2 ≤ Y 0 ∧ Y 0 ≤ 6) → |Y 1| ≤ ε → |Y 2| ≤ ε →
      coreRadiusReturnValid Y ∧ ContDiffAt ℝ 2 coreRadiusReturnTime Y ∧
        ContDiffAt ℝ 2 (coreReturnState coreRadiusReturnTime) Y ∧
        ‖fderiv ℝ coreRadiusReturnTime Y‖ +
          ‖fderiv ℝ (coreReturnState coreRadiusReturnTime) Y‖ +
          ‖fderiv ℝ (fderiv ℝ coreRadiusReturnTime) Y‖ +
          ‖fderiv ℝ (fderiv ℝ (coreReturnState coreRadiusReturnTime)) Y‖ ≤ C ∧
        (∀ᶠ Z in 𝓝 Y, coreRadiusReturnValid Z ∧ ContDiffAt ℝ 2 coreRadiusReturnTime Z ∧
          ContDiffAt ℝ 2 (coreReturnState coreRadiusReturnTime) Z) := by
  let P := coreReturnState coreRadiusReturnTime
  let G : Set CoreAngleState := {Y | coreRadiusReturnValid Y ∧
    ContDiffAt ℝ 2 coreRadiusReturnTime Y ∧ ContDiffAt ℝ 2 P Y}
  let S : Set CoreAngleState := (fun k : ℝ => (![k, 0, 0] : CoreAngleState)) '' Icc 2 6
  have hcS : IsCompact S := isCompact_Icc.image (by fun_prop)
  have hSG : S ⊆ interior G := by
    rintro Y ⟨k, hk, rfl⟩
    obtain ⟨_, ht, hP, hvalid⟩ := coreRadiusReturn_reference_regular (by linarith only [hk.1])
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hvalid, ht.eventually (by norm_num), hP.eventually (by norm_num)] with Z hz htZ hPZ
    exact ⟨hz, htZ, hPZ⟩
  obtain ⟨ε, hε, hεG⟩ := hcS.exists_cthickening_subset_open isOpen_interior hSG
  let W := cthickening ε S
  have hWG : W ⊆ G := hεG.trans interior_subset
  let b : CoreAngleState → ℝ := fun Y => ‖fderiv ℝ coreRadiusReturnTime Y‖ +
    ‖fderiv ℝ P Y‖ + ‖fderiv ℝ (fderiv ℝ coreRadiusReturnTime) Y‖ + ‖fderiv ℝ (fderiv ℝ P) Y‖
  have hcb : ContinuousOn b W := by
    intro Y hY
    obtain ⟨_, ht, hP⟩ := hWG hY
    have ht' := ht.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    have hP' := hP.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact ((((ht.continuousAt_fderiv (by norm_num)).norm.add
      (hP.continuousAt_fderiv (by norm_num)).norm).add
      (ht'.continuousAt_fderiv (by norm_num)).norm).add
      (hP'.continuousAt_fderiv (by norm_num)).norm).continuousWithinAt
  obtain ⟨B, hB⟩ := hcS.cthickening.exists_bound_of_continuousOn hcb
  refine ⟨ε, hε, max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro Y hk hu hw
  have hdist : dist Y (![Y 0, 0, 0] : CoreAngleState) ≤ ε := by
    apply (dist_pi_le_iff hε.le).mpr
    intro i
    fin_cases i
    · simpa using hε.le
    · simpa [Real.dist_eq] using hu
    · simpa [Real.dist_eq] using hw
  have hYS : (![Y 0, 0, 0] : CoreAngleState) ∈ S := ⟨Y 0, hk, rfl⟩
  have hYW : Y ∈ W := mem_cthickening_of_dist_le Y _ ε S hYS hdist
  obtain ⟨hvalid, ht, hP⟩ := hWG hYW
  exact ⟨hvalid, ht, hP, (le_abs_self (b Y)).trans ((hB Y hYW).trans (le_max_left _ _)),
    mem_interior_iff_mem_nhds.mp (hεG hYW)⟩
