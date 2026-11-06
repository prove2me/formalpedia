-- Prove2me | solution 1 for BianchiIX.coreRegion_exit_factor_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T01:59:39.635181+00:00
-- url     : https://prove2.me/submissions/52b62062-035a-4944-a6ed-b003f6947025

import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_Dynamics_CoreExitFactor
import Theorems.Thm_BianchiIX_coreBootstrap_coefficient_scales
import Theorems.Thm_BianchiIX_coreBootstrap_radius_closed
import Theorems.Thm_BianchiIX_coreRegion_exit_radius_velocity
import Theorems.Thm_BianchiIX_radial_arrival_factor_bounds
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Module
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
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

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_sq (m v : ℝ) : coreRadius m v ^ 2 = coreEnergy m v :=
  Real.sq_sqrt (by unfold coreEnergy; positivity)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_pos {m v : ℝ} (hv : 0 < v) : 0 < coreRadius m v := by
  apply Real.sqrt_pos.mpr
  unfold coreEnergy
  positivity

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreAngle_sqrt {m v : ℝ} (hv : 0 < v) :
    Real.sqrt (1 + ((1 - m) / v) ^ 2) = coreRadius m v / v := by
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (div_nonneg (coreRadius_pos hv).le hv.le)).mpr
  simp only [div_pow, coreRadius_sq]
  unfold coreEnergy
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.tanh_coreAngle {m v : ℝ} (hv : 0 < v) :
    Real.tanh (coreAngle m v) = (1 - m) / coreRadius m v := by
  rw [coreAngle, Real.tanh_arsinh, coreAngle_sqrt hv]
  field_simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.core_section_phase_gap {k m : ℝ} (hk : 6 ≤ k)
    (hr : 99 / 100 * k ≤ coreRadius m 1) : 3 * k / 4 ≤ |m - 1| := by
  have hr2 := (sq_le_sq₀ (by linarith : 0 ≤ 99 / 100 * k)
    (show 0 ≤ coreRadius m 1 from Real.sqrt_nonneg _)).mpr hr
  rw [coreRadius_sq] at hr2
  unfold coreEnergy at hr2
  apply (sq_le_sq₀ (by linarith : 0 ≤ 3 * k / 4) (abs_nonneg _)).mp
  rw [sq_abs]
  nlinarith [sq_nonneg (k - 6)]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRegion_radius_bounds {k : ℝ} {y : ProjectiveState} (hk : 6 ≤ k) (hy : coreRegion k y) :
    99 / 100 * k ≤ coreRadius (y 0) (y 2) ∧ coreRadius (y 0) (y 2) ≤ 101 / 100 * k :=
  coreBootstrap_radius_closed hk (Real.sqrt_nonneg _)
    (by rw [coreRadius_sq]; exact hy.1)

end
end

theorem solution {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hV : y 2 = 1) (hM : y 0 < 1) :
    0 < coreExitRadialFactor y ∧ coreExitRadialFactor y ≤ 1 ∧
      |coreExitRadialFactor y - 1| ≤ 8 * (y 1 / k + y 3 ^ 2 / k ^ 2) := by
  let r := coreRadius (y 0) (y 2)
  let c := -Real.tanh (coreAngle (y 0) (y 2))
  let f := coreAngleField (coreAngle (y 0) (y 2)) (toCoreAngleState y) 0
  have hv : 0 < y 2 := by rw [hV]; norm_num
  have hk0 : 0 < k := by linarith only [hk]
  have hr0 : 0 < r := coreRadius_pos hv
  have hr := coreRegion_radius_bounds hk hy
  have hgap := core_section_phase_gap hk (show 99 / 100 * k ≤ coreRadius (y 0) 1 by simpa only [hV] using hr.1)
  rw [abs_of_neg (sub_neg.mpr hM)] at hgap
  have hc : c ≤ -1 / 2 := by
    have hid : c = (y 0 - 1) / r := by dsimp [c]; rw [tanh_coreAngle hv]; dsimp [r]; ring
    rw [hid]
    apply (div_le_iff₀ hr0).mpr
    change y 0 - 1 ≤ (-1 / 2) * coreRadius (y 0) (y 2)
    linarith only [hgap, hr.2, hk]
  obtain ⟨hf, hfbound⟩ := coreRegion_exit_radius_velocity hk hy hV hM
  change f ≤ 0 at hf
  change |f| ≤ 2 * (y 1 + y 3 ^ 2 / r) at hfbound
  obtain ⟨_, hpos, hle, herr⟩ := radial_arrival_factor_bounds hr0 hc hf
  refine ⟨hpos, hle, herr.trans ?_⟩
  obtain ⟨_, _, _, _, _, hkr, hk2r2, _⟩ := coreBootstrap_coefficient_scales hk hr
  have hu0 := hy.2.2.1.1
  have huScale : y 1 / r ≤ (3 / 2) * (y 1 / k) := by
    calc
      _ = (k / r) * (y 1 / k) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hkr (div_nonneg hu0 hk0.le)
  have hwScale : y 3 ^ 2 / r ^ 2 ≤ (3 / 2) * (y 3 ^ 2 / k ^ 2) := by
    calc
      _ = (k ^ 2 / r ^ 2) * (y 3 ^ 2 / k ^ 2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hk2r2 (by positivity)
  calc
    2 * |f| / r ≤ 2 * (2 * (y 1 + y 3 ^ 2 / r)) / r := by gcongr
    _ = 4 * (y 1 / r + y 3 ^ 2 / r ^ 2) := by field_simp; ring
    _ ≤ 8 * (y 1 / k + y 3 ^ 2 / k ^ 2) := by
      linarith only [huScale, hwScale, div_nonneg hu0 hk0.le,
        div_nonneg (sq_nonneg (y 3)) (sq_nonneg k)]
