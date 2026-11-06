-- Prove2me | solution 1 for BianchiIX.coreRadiusEntry_variation_norm
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:01:38.211419+00:00
-- url     : https://prove2.me/submissions/8921d24d-59b0-4c2c-b823-1984624df1e7

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreWeightedVariation
import Definitions.Def_BianchiIX_Dynamics_CoreFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Theorems.Thm_BianchiIX_coreRadiusEntry_variation_bounds
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

private theorem BianchiIX.coreBootstrap_wall_bound {k u : ℝ} (hk : 6 ≤ k) (hu : u ≤ (1 / 10000) / k) :
    u ≤ 1 / 60000 := by
  have hk0 : 0 < k := by linarith
  exact hu.trans ((div_le_iff₀ hk0).mpr (by linarith))

end
end

theorem solution {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) (v : CoreAngleState) :
    ‖scaleCoreVariation (Y 0)
      (coreClockProjection (coreRadiusEntry Y) (fderiv ℝ coreRadiusEntry Y v))‖ ≤
        2 * (|v 0| + Y 0 * |v 1| + |v 2|) := by
  let k := Y 0
  let xi := coreClockProjection (coreRadiusEntry Y) (fderiv ℝ coreRadiusEntry Y v)
  have hk0 : 0 < k := by dsimp [k]; linarith only [hk]
  have hu1 : Y 1 ≤ 1 := (coreBootstrap_wall_bound hk hu.2).trans (by norm_num)
  have hw1 : Y 2 ≤ 1 := (coreBootstrap_wall_bound hk hw.2).trans (by norm_num)
  have hw2 : Y 2 ^ 2 ≤ 1 := by nlinarith only [hw.1, hw1]
  have hku : k * Y 1 ≤ 1 / 10000 := by
    have H := (le_div_iff₀ hk0).mp hu.2
    linarith only [H]
  have huk : Y 1 / k ≤ 1 / 6 := (div_le_iff₀ hk0).mpr (by dsimp [k]; linarith only [hu1, hk])
  have hwk : Y 2 ^ 2 / k ^ 2 ≤ 1 / 36 := (div_le_iff₀ (sq_pos_of_pos hk0)).mpr (by
    dsimp [k]
    nlinarith only [hw2, hk, sq_nonneg (Y 0 - 6)])
  have hsmallR : 4 * (Y 1 / k + Y 2 ^ 2 / k ^ 2) ≤ 1 := by linarith only [huk, hwk]
  have hsmallU : 4 * k * Y 1 ≤ 1 := by linarith only [hku]
  have hsmallP : 8 * Y 2 / k ^ 2 ≤ 1 := (div_le_iff₀ (sq_pos_of_pos hk0)).mpr (by
    dsimp [k]
    nlinarith only [hw1, hk, sq_nonneg (Y 0 - 6)])
  obtain ⟨hR, hU, hP⟩ := coreRadiusEntry_variation_bounds hk hu hw v
  change |xi 0 - v 0| ≤ 4 * (Y 1 / k + Y 2 ^ 2 / k ^ 2) * |v 0| at hR
  change |k * xi 1| ≤ k * |v 1| + 4 * k * Y 1 * |v 0| at hU
  change |xi 2 - v 2| ≤ 8 * Y 2 / k ^ 2 * |v 0| at hP
  have hR' : |xi 0 - v 0| ≤ |v 0| := hR.trans (mul_le_of_le_one_left (abs_nonneg _) hsmallR)
  have hU' : |k * xi 1| ≤ k * |v 1| + |v 0| :=
    hU.trans (add_le_add (le_refl _) (mul_le_of_le_one_left (abs_nonneg _) hsmallU))
  have hP' : |xi 2 - v 2| ≤ |v 0| := hP.trans (mul_le_of_le_one_left (abs_nonneg _) hsmallP)
  have htri (i : Fin 3) : |xi i| ≤ |xi i - v i| + |v i| := by
    simpa only [sub_add_cancel] using abs_add_le (xi i - v i) (v i)
  apply (pi_norm_le_iff_of_nonempty _).mpr
  intro i
  fin_cases i
  · change |xi 0| ≤ _
    nlinarith only [htri 0, hR', abs_nonneg (v 0), abs_nonneg (v 2), mul_nonneg hk0.le (abs_nonneg (v 1))]
  · change |k * xi 1| ≤ _
    nlinarith only [hU', abs_nonneg (v 0), abs_nonneg (v 2), mul_nonneg hk0.le (abs_nonneg (v 1))]
  · change |xi 2| ≤ _
    nlinarith only [htri 2, hP', abs_nonneg (v 0), abs_nonneg (v 2), mul_nonneg hk0.le (abs_nonneg (v 1))]
