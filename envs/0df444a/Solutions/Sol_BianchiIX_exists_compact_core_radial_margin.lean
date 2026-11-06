-- Prove2me | solution 1 for BianchiIX.exists_compact_core_radial_margin
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T03:48:50.648102+00:00
-- url     : https://prove2.me/submissions/72cea21f-22fa-4e48-accd-e48d05a9a8e0

import Definitions.Def_BianchiIX_Dynamics_ReferenceReturn
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Theorems.Thm_BianchiIX_coreRadiusReturn_reference_radial_derivative
import Theorems.Thm_BianchiIX_coreRadiusReturn_reference_regular
import Theorems.Thm_BianchiIX_exists_compact_core_return_two_germ
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
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
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.exists_compact_core_return_two :
    ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (2 ≤ Y 0 ∧ Y 0 ≤ 6) → |Y 1| ≤ ε → |Y 2| ≤ ε →
      coreRadiusReturnValid Y ∧ ContDiffAt ℝ 2 coreRadiusReturnTime Y ∧
        ContDiffAt ℝ 2 (coreReturnState coreRadiusReturnTime) Y ∧
        ‖fderiv ℝ coreRadiusReturnTime Y‖ +
          ‖fderiv ℝ (coreReturnState coreRadiusReturnTime) Y‖ +
          ‖fderiv ℝ (fderiv ℝ coreRadiusReturnTime) Y‖ +
          ‖fderiv ℝ (fderiv ℝ (coreReturnState coreRadiusReturnTime)) Y‖ ≤ C := by
  obtain ⟨ε, hε, C, hC, h⟩ := exists_compact_core_return_two_germ
  refine ⟨ε, hε, C, hC, ?_⟩
  intro Y hk hu hw
  have H := h Y hk hu hw
  exact ⟨H.1, H.2.1, H.2.2.1, H.2.2.2.1⟩

end
end

theorem solution {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (2 ≤ Y 0 ∧ Y 0 ≤ 6) → |Y 1| ≤ ε → |Y 2| ≤ ε →
      |(fderiv ℝ (coreReturnState coreRadiusReturnTime) Y (Pi.single 0 1)) 0 - 1| ≤ δ ∧
        ‖fderiv ℝ (coreReturnState coreRadiusReturnTime) Y‖ ≤ C := by
  let F := coreReturnState coreRadiusReturnTime
  let S : Set CoreAngleState := (fun k : ℝ => (![k, 0, 0] : CoreAngleState)) '' Icc 2 6
  let G : Set CoreAngleState := {Y | |(fderiv ℝ F Y (Pi.single 0 1)) 0 - 1| < δ}
  have hS : IsCompact S := isCompact_Icc.image (by fun_prop)
  have hSG : S ⊆ interior G := by
    rintro Y ⟨k, hk, rfl⟩
    have hk1 : 1 < k := by linarith only [hk.1]
    have hc := ((coreRadiusReturn_reference_regular hk1).2.2.1.continuousAt_fderiv (by norm_num)).clm_apply
      (continuousAt_const (y := (Pi.single 0 1 : CoreAngleState)))
    have hcr := ((continuousAt_pi.mp hc 0).sub (continuousAt_const (y := (1 : ℝ)))).abs
    apply mem_interior_iff_mem_nhds.mpr
    apply hcr.eventually (isOpen_Iio.mem_nhds _)
    change |(fderiv ℝ F ![k, 0, 0] (Pi.single 0 1)) 0 - 1| < δ
    simpa only [F, coreRadiusReturn_reference_radial_derivative hk1, Pi.single_eq_same,
      sub_self, abs_zero] using hδ
  obtain ⟨ρ, hρ, hρG⟩ := hS.exists_cthickening_subset_open isOpen_interior hSG
  obtain ⟨ε₀, hε₀, C, hC, hbox⟩ := exists_compact_core_return_two
  refine ⟨min ε₀ ρ, lt_min hε₀ hρ, C, hC, ?_⟩
  intro Y hk hu hw
  have hdist : dist Y (![Y 0, 0, 0] : CoreAngleState) ≤ ρ := by
    apply (dist_pi_le_iff hρ.le).mpr
    intro i
    fin_cases i
    · simpa using hρ.le
    · simpa [Real.dist_eq] using hu.trans (min_le_right ε₀ ρ)
    · simpa [Real.dist_eq] using hw.trans (min_le_right ε₀ ρ)
  have hnear : Y ∈ G := interior_subset (hρG
    (mem_cthickening_of_dist_le Y _ ρ S ⟨Y 0, hk, rfl⟩ hdist))
  refine ⟨hnear.le, ?_⟩
  have H := (hbox Y hk (hu.trans (min_le_left _ _)) (hw.trans (min_le_left _ _))).2.2.2
  linarith only [H, norm_nonneg (fderiv ℝ coreRadiusReturnTime Y),
    norm_nonneg (fderiv ℝ (fderiv ℝ coreRadiusReturnTime) Y), norm_nonneg (fderiv ℝ (fderiv ℝ F) Y)]
