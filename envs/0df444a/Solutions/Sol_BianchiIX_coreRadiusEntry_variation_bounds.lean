-- Prove2me | solution 1 for BianchiIX.coreRadiusEntry_variation_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T01:59:12.718467+00:00
-- url     : https://prove2.me/submissions/7bf141cf-744f-4710-b44d-f735d5de96b0

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Theorems.Thm_BianchiIX_coreCoordinate_fderiv
import Theorems.Thm_BianchiIX_coreRadiusEntry_fderiv
import Theorems.Thm_BianchiIX_coreRadiusEntry_field_bounds
import Theorems.Thm_BianchiIX_coreRadiusEntry_state_differential
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

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRadius_coreRadiusEntry {Y : CoreAngleState} (hk : 1 < Y 0) :
    coreRadius (coreRadiusEntry Y 0) (coreRadiusEntry Y 2) = Y 0 := by
  have hk0 : 0 < Y 0 := lt_trans zero_lt_one hk
  have hsq := Real.sq_sqrt (by nlinarith only [hk] : 0 ≤ Y 0 ^ 2 - 1)
  have he : coreEnergy (coreRadiusEntry Y 0) (coreRadiusEntry Y 2) = Y 0 ^ 2 := by
    dsimp [coreRadiusEntry, coreEnergy]
    nlinarith only [hsq]
  rw [coreRadius, he, Real.sqrt_sq hk0.le]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.toCoreAngleState_coreRadiusEntry {Y : CoreAngleState} (hk : 1 < Y 0) :
    toCoreAngleState (coreRadiusEntry Y) = Y := by
  ext i
  fin_cases i
  · exact coreRadius_coreRadiusEntry hk
  · rfl
  · simp [toCoreAngleState, coreRadiusEntry]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRadiusEntry_angle_differential {Y : CoreAngleState} (hk : 1 < Y 0) (v : CoreAngleState) :
    fderiv ℝ projectiveCoreAngle (coreRadiusEntry Y) (fderiv ℝ coreRadiusEntry Y v) =
      -v 0 / Real.sqrt (Y 0 ^ 2 - 1) := by
  have hk0 : Y 0 ≠ 0 := ne_of_gt (lt_trans zero_lt_one hk)
  rw [(coreCoordinate_fderiv (show 0 < coreRadiusEntry Y 2 by change (0 : ℝ) < 1; norm_num) _).2,
    coreRadius_coreRadiusEntry hk, coreRadiusEntry_fderiv hk]
  dsimp [coreRadiusEntry]
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRadiusEntry_projection {Y : CoreAngleState} (hk : 1 < Y 0) (v : CoreAngleState) :
    coreClockProjection (coreRadiusEntry Y) (fderiv ℝ coreRadiusEntry Y v) =
      v + (v 0 / Real.sqrt (Y 0 ^ 2 - 1)) • coreAngleField (projectiveCoreAngle (coreRadiusEntry Y)) Y := by
  have hstate := congrArg (fun L : CoreAngleState →L[ℝ] CoreAngleState => L v)
    (coreRadiusEntry_state_differential hk)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hstate
  rw [coreClockProjection, hstate, coreRadiusEntry_angle_differential hk,
    toCoreAngleState_coreRadiusEntry hk, neg_div, neg_smul, sub_neg_eq_add]

end
end

private theorem BianchiIX.coreRadiusEntry_gap {k : ℝ} (hk : 6 ≤ k) : k / 2 ≤ Real.sqrt (k ^ 2 - 1) := by
  have hs := Real.sq_sqrt (by nlinarith only [hk] : 0 ≤ k ^ 2 - 1)
  have hnonneg := Real.sqrt_nonneg (k ^ 2 - 1)
  by_contra! hlt
  have H := (sq_lt_sq₀ hnonneg (by linarith only [hk] : 0 ≤ k / 2)).mpr hlt
  nlinarith only [hs, H, hk, sq_nonneg (k - 6)]

/-- All three moving-entry errors retain their actual wall amplitudes. -/
theorem solution {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) (v : CoreAngleState) :
    let xi := coreClockProjection (coreRadiusEntry Y) (fderiv ℝ coreRadiusEntry Y v)
    |xi 0 - v 0| ≤ 4 * (Y 1 / Y 0 + Y 2 ^ 2 / Y 0 ^ 2) * |v 0| ∧
      |Y 0 * xi 1| ≤ Y 0 * |v 1| + 4 * Y 0 * Y 1 * |v 0| ∧
      |xi 2 - v 2| ≤ 8 * Y 2 / Y 0 ^ 2 * |v 0| := by
  intro xi
  let k := Y 0
  let f := coreAngleField (projectiveCoreAngle (coreRadiusEntry Y)) Y
  have hk0 : 0 < k := by dsimp [k]; linarith only [hk]
  have hgap := coreRadiusEntry_gap hk
  have hs : 0 < Real.sqrt (k ^ 2 - 1) := lt_of_lt_of_le (by positivity : 0 < k / 2) hgap
  have hratio : |v 0 / Real.sqrt (k ^ 2 - 1)| ≤ 2 * |v 0| / k := by
    rw [abs_div, abs_of_pos hs]
    exact (div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hgap).trans_eq (by ring)
  have hproj := coreRadiusEntry_projection (by linarith only [hk] : 1 < Y 0) v
  have hid (i : Fin 3) : xi i - v i = (v 0 / Real.sqrt (k ^ 2 - 1)) * f i := by
    change coreClockProjection (coreRadiusEntry Y) (fderiv ℝ coreRadiusEntry Y v) i - v i = _
    rw [hproj]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left]
    rfl
  obtain ⟨hR, hU, hP⟩ := coreRadiusEntry_field_bounds hk hu hw
  change |f 0| ≤ 2 * (Y 1 + Y 2 ^ 2 / k) at hR
  change |f 1| ≤ 2 * k * Y 1 at hU
  change |f 2| ≤ 4 * Y 2 / k at hP
  have hbound (i : Fin 3) : |xi i - v i| ≤ (2 * |v 0| / k) * |f i| := by
    rw [hid i, abs_mul]
    exact mul_le_mul_of_nonneg_right hratio (abs_nonneg _)
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ ≤ (2 * |v 0| / k) * |f 0| := hbound 0
      _ ≤ (2 * |v 0| / k) * (2 * (Y 1 + Y 2 ^ 2 / k)) := by gcongr
      _ = _ := by dsimp [k]; field_simp; ring
  · have H : |xi 1| ≤ |v 1| + (2 * |v 0| / k) * (2 * k * Y 1) := by
      calc
        _ ≤ |v 1| + |xi 1 - v 1| := by
          convert! abs_add_le (v 1) (xi 1 - v 1) using 1
          congr 1
          ring
        _ ≤ _ := add_le_add (le_refl _) ((hbound 1).trans (mul_le_mul_of_nonneg_left hU (by positivity)))
    rw [abs_mul, abs_of_pos hk0]
    have H' := mul_le_mul_of_nonneg_left H hk0.le
    convert! H' using 1
    dsimp [k]
    field_simp
    ring
  · calc
      _ ≤ (2 * |v 0| / k) * |f 2| := hbound 2
      _ ≤ (2 * |v 0| / k) * (4 * Y 2 / k) := by gcongr
      _ = _ := by dsimp [k]; field_simp; ring
