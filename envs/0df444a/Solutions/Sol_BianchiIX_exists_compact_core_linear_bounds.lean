-- Prove2me | solution 1 for BianchiIX.exists_compact_core_linear_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T03:46:08.293401+00:00
-- url     : https://prove2.me/submissions/2020c9ba-16b1-4e23-936e-48eb5917efec

import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Theorems.Thm_BianchiIX_coreRadiusReturn_reference_value
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
open Set

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

/-- The actual compact-core map and its first derivative differ linearly from the zero-wall slice. -/
theorem solution :
    ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (2 ≤ Y 0 ∧ Y 0 ≤ 6) → |Y 1| ≤ ε → |Y 2| ≤ ε →
      let F := coreReturnState coreRadiusReturnTime
      let Z : CoreAngleState := ![Y 0, 0, 0]
      coreRadiusReturnValid Y ∧ ContDiffAt ℝ 2 F Y ∧
        ‖F Y - Z‖ ≤ C * (|Y 1| + |Y 2|) ∧
        ‖fderiv ℝ F Y - fderiv ℝ F Z‖ ≤ C * (|Y 1| + |Y 2|) ∧
        ‖fderiv ℝ F Y‖ ≤ C := by
  obtain ⟨ε, hε, C, hC, H⟩ := exists_compact_core_return_two
  let F := coreReturnState coreRadiusReturnTime
  let S : Set CoreAngleState := Icc (![2, -ε, -ε] : CoreAngleState) ![6, ε, ε]
  have hcoords {Y : CoreAngleState} (hY : Y ∈ S) :
      (2 ≤ Y 0 ∧ Y 0 ≤ 6) ∧ |Y 1| ≤ ε ∧ |Y 2| ≤ ε :=
    ⟨⟨hY.1 0, hY.2 0⟩, abs_le.mpr ⟨hY.1 1, hY.2 1⟩,
      abs_le.mpr ⟨hY.1 2, hY.2 2⟩⟩
  have hmem {Y : CoreAngleState} (hk : 2 ≤ Y 0 ∧ Y 0 ≤ 6)
      (hu : |Y 1| ≤ ε) (hw : |Y 2| ≤ ε) : Y ∈ S := by
    constructor
    · intro i
      fin_cases i
      · exact hk.1
      · exact (abs_le.mp hu).1
      · exact (abs_le.mp hw).1
    · intro i
      fin_cases i
      · exact hk.2
      · exact (abs_le.mp hu).2
      · exact (abs_le.mp hw).2
  have HR (Y : CoreAngleState) (hY : Y ∈ S) :=
    H Y (hcoords hY).1 (hcoords hY).2.1 (hcoords hY).2.2
  have HD (Y : CoreAngleState) (hY : Y ∈ S) : DifferentiableAt ℝ F Y :=
    (HR Y hY).2.2.1.differentiableAt (by norm_num)
  have HD₂ (Y : CoreAngleState) (hY : Y ∈ S) : DifferentiableAt ℝ (fderiv ℝ F) Y :=
    ((HR Y hY).2.2.1.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have HB (Y : CoreAngleState) (hY : Y ∈ S) :
      ‖fderiv ℝ F Y‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ F) Y‖ ≤ C := by
    have HH := (HR Y hY).2.2.2
    constructor <;> linarith only [HH, norm_nonneg (fderiv ℝ coreRadiusReturnTime Y),
      norm_nonneg (fderiv ℝ F Y), norm_nonneg (fderiv ℝ (fderiv ℝ coreRadiusReturnTime) Y),
      norm_nonneg (fderiv ℝ (fderiv ℝ F) Y)]
  refine ⟨ε, hε, C, hC, ?_⟩
  intro Y hk hu hw F' Z
  have hY : Y ∈ S := hmem hk hu hw
  have hZ : Z ∈ S := hmem hk (by simpa [Z] using hε.le) (by simpa [Z] using hε.le)
  have hdist : ‖Y - Z‖ ≤ |Y 1| + |Y 2| := by
    apply (pi_norm_le_iff_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))).mpr
    intro i
    fin_cases i
    · change |Y 0 - Y 0| ≤ |Y 1| + |Y 2|
      simpa only [sub_self, abs_zero] using add_nonneg (abs_nonneg (Y 1)) (abs_nonneg (Y 2))
    · change |Y 1 - 0| ≤ |Y 1| + |Y 2|
      simpa only [sub_zero] using le_add_of_nonneg_right (abs_nonneg (Y 2))
    · change |Y 2 - 0| ≤ |Y 1| + |Y 2|
      simpa only [sub_zero] using le_add_of_nonneg_left (abs_nonneg (Y 1))
  have HV := Convex.norm_image_sub_le_of_norm_fderiv_le HD (fun X hX => (HB X hX).1)
    (convex_Icc _ _) hZ hY
  have HJ := Convex.norm_image_sub_le_of_norm_fderiv_le HD₂ (fun X hX => (HB X hX).2)
    (convex_Icc _ _) hZ hY
  have hFZ : F Z = Z := coreRadiusReturn_reference_value (by linarith only [hk.1])
  rw [hFZ] at HV
  exact ⟨(HR Y hY).1, (HR Y hY).2.2.1,
    HV.trans (mul_le_mul_of_nonneg_left hdist hC.le),
    HJ.trans (mul_le_mul_of_nonneg_left hdist hC.le), (HB Y hY).1⟩
