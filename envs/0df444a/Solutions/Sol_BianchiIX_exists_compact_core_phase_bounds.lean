-- Prove2me | solution 1 for BianchiIX.exists_compact_core_phase_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T03:50:56.132366+00:00
-- url     : https://prove2.me/submissions/0ffd689e-7c99-4bf2-919a-520cb4ca7bfd

import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Theorems.Thm_BianchiIX_coreRadiusReturn_reference_radial_derivative
import Theorems.Thm_BianchiIX_exists_compact_core_linear_bounds
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


/-- Compact-core phase errors retain the incoming amplitude and its square root along the cone. -/
theorem solution :
    ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (2 ≤ Y 0 ∧ Y 0 ≤ 6) → (0 ≤ Y 1 ∧ Y 1 ≤ ε) → (0 ≤ Y 2 ∧ Y 2 ≤ ε) →
      let F := coreReturnState coreRadiusReturnTime
      coreRadiusReturnValid Y ∧ ContDiffAt ℝ 2 F Y ∧
        |F Y 0 - Y 0| ≤ C * (Y 1 + Y 2) / Y 0 ∧
        ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
          |fderiv ℝ F Y v 0 - 1| ≤ C * Real.sqrt (Y 1 + Y 2) / Y 0 := by
  obtain ⟨ε, hε, C, hC, H⟩ := exists_compact_core_linear_bounds
  refine ⟨min ε (1 / 2), lt_min hε (by norm_num), 12 * C, by positivity, ?_⟩
  intro Y hk hu hw F
  obtain ⟨hvalid, hF, hval, hdiff, hnorm⟩ := H Y hk
    ((abs_of_nonneg hu.1).le.trans (hu.2.trans (min_le_left _ _)))
    ((abs_of_nonneg hw.1).le.trans (hw.2.trans (min_le_left _ _)))
  rw [abs_of_nonneg hu.1, abs_of_nonneg hw.1] at hval hdiff
  let Z : CoreAngleState := ![Y 0, 0, 0]
  let D := fderiv ℝ F Y
  let v₀ : CoreAngleState := Pi.single 0 1
  have hb : 0 ≤ Y 1 + Y 2 := add_nonneg hu.1 hw.1
  have hb1 : Y 1 + Y 2 ≤ 1 := by
    linarith only [hu.2.trans (min_le_right _ _), hw.2.trans (min_le_right _ _)]
  have hbs : Y 1 + Y 2 ≤ Real.sqrt (Y 1 + Y 2) := by
    have hs := Real.sqrt_le_one.mpr hb1
    nlinarith only [Real.sq_sqrt hb, Real.sqrt_nonneg (Y 1 + Y 2),
      mul_nonneg (Real.sqrt_nonneg (Y 1 + Y 2)) (sub_nonneg.mpr hs)]
  have hk0 : 0 < Y 0 := by linarith only [hk.1]
  have hval0 : |F Y 0 - Y 0| ≤ C * (Y 1 + Y 2) :=
    (show |F Y 0 - Y 0| ≤ ‖F Y - Z‖ from norm_le_pi_norm (F Y - Z) 0).trans hval
  refine ⟨hvalid, hF, hval0.trans ?_, ?_⟩
  · apply (le_div_iff₀ hk0).mpr
    have Hk := mul_le_mul_of_nonneg_left hk.2 (mul_nonneg hC.le hb)
    nlinarith only [Hk, mul_nonneg hC.le hb]
  · intro v hv hvu hvw
    have hcol : |D v₀ 0 - 1| ≤ C * (Y 1 + Y 2) := by
      have he : fderiv ℝ F Z v₀ = v₀ :=
        coreRadiusReturn_reference_radial_derivative (by linarith only [hk.1] : 1 < Y 0)
      have H₀ := norm_le_pi_norm ((D - fderiv ℝ F Z) v₀) 0
      have H₁ := (D - fderiv ℝ F Z).le_opNorm v₀
      have H₂ := H₀.trans H₁
      simp only [sub_apply, Pi.sub_apply, he, v₀, Pi.single_eq_same, Real.norm_eq_abs,
        Pi.norm_single, norm_one, mul_one] at H₂
      exact H₂.trans hdiff
    have hvdiff : ‖v - v₀‖ ≤ Real.sqrt (Y 1 + Y 2) := by
      apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
      intro i
      fin_cases i
      · simp [v₀, hv, Real.sqrt_nonneg]
      · simpa [v₀] using hvu.trans (Real.sqrt_le_sqrt (le_add_of_nonneg_right hw.1))
      · simpa [v₀] using hvw.trans (Real.sqrt_le_sqrt (le_add_of_nonneg_left hu.1))
    have hwall : |D (v - v₀) 0| ≤ C * Real.sqrt (Y 1 + Y 2) :=
      ((norm_le_pi_norm (D (v - v₀)) 0).trans (D.le_opNorm _)).trans
        (mul_le_mul hnorm hvdiff (norm_nonneg _) hC.le)
    have htotal : |D v 0 - 1| ≤ 2 * C * Real.sqrt (Y 1 + Y 2) := by
      have Hsplit : D v 0 - 1 = (D v₀ 0 - 1) + D (v - v₀) 0 := by rw [map_sub]; simp
      rw [Hsplit]
      have H₀ := (abs_add_le _ _).trans (add_le_add hcol hwall)
      nlinarith only [H₀, mul_le_mul_of_nonneg_left hbs hC.le]
    apply htotal.trans
    apply (le_div_iff₀ hk0).mpr
    have Hk := mul_le_mul_of_nonneg_left hk.2 (by positivity : 0 ≤ 2 * C * Real.sqrt (Y 1 + Y 2))
    nlinarith only [Hk]
