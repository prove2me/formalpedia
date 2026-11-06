-- Prove2me | solution 1 for BianchiIX.entranceWeakQuadratic_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T16:25:03.273108+00:00
-- url     : https://prove2.me/submissions/b39a5e3f-868a-4807-b326-bed006001e4e

import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_EntranceRegion
import Definitions.Def_BianchiIX_EntrancePhaseResponseData
import Theorems.Thm_BianchiIX_entrance_phase_bounds
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.Deriv.Pi

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.entranceRegion_phase {k : ℝ} {y : ProjectiveState} (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) :
    4 / 5 * k ≤ y 0 - 1 ∧ y 0 - 1 ≤ 101 / 100 * k :=
  entrance_phase_bounds hk hy.1 hy.2.1 hy.2.2.2.1

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.entranceWeakQuadratic_differential {y : ProjectiveState} (hm : y 0 + 1 ≠ 0) :
    DifferentiableAt ℝ entranceWeakQuadratic y ∧ ∀ v : ProjectiveState,
      fderiv ℝ entranceWeakQuadratic y v =
        (2 * y 1 ^ 2 - 8 * y 1 * y 3 + 2 * y 3 ^ 2) / (y 0 + 1) ^ 3 * v 0 +
        (2 * (1 - 1 / (y 0 + 1) ^ 2) * y 1 + (-1 + 4 / (y 0 + 1) ^ 2) * y 3) * v 1 +
        ((-1 + 4 / (y 0 + 1) ^ 2) * y 1 - 2 * y 3 / (y 0 + 1) ^ 2) * v 3 := by
  have hi : HasDerivAt (fun t : ℝ => 1 / (t + 1) ^ 2) (-2 / (y 0 + 1) ^ 3) (y 0) := by
    apply ((hasDerivAt_const (y 0) (1 : ℝ)).div (((hasDerivAt_id (y 0)).add_const 1).pow 2)
      (pow_ne_zero 2 hm)).congr_deriv
    dsimp
    field_simp
    ring
  have hd (i : Fin 4) := hasFDerivAt_apply (𝕜 := ℝ) i y
  have hI := hi.comp_hasFDerivAt y (hd 0)
  have hA := (hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) y).sub hI
  have hC := (hasFDerivAt_const (𝕜 := ℝ) (-1 : ℝ) y).add (hI.const_mul 4)
  have H := ((hA.mul ((hd 1).pow 2)).add ((hC.mul (hd 1)).mul (hd 3))).sub (((hd 3).pow 2).mul hI)
  have heq : entranceWeakQuadratic = fun z => (1 - 1 / (z 0 + 1) ^ 2) * z 1 ^ 2 +
      (-1 + 4 * (1 / (z 0 + 1) ^ 2)) * z 1 * z 3 - z 3 ^ 2 * (1 / (z 0 + 1) ^ 2) := by
    funext z
    unfold entranceWeakQuadratic
    ring
  change HasFDerivAt (fun z => (1 - 1 / (z 0 + 1) ^ 2) * z 1 ^ 2 +
    (-1 + 4 * (1 / (z 0 + 1) ^ 2)) * z 1 * z 3 - z 3 ^ 2 * (1 / (z 0 + 1) ^ 2)) _ y at H
  rw [← heq] at H
  refine ⟨H.differentiableAt, fun v => ?_⟩
  rw [H.fderiv]
  simp [sub_apply, add_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply, Function.comp_def]
  ring

end
end

theorem solution {k : ℝ} {y : ProjectiveState}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) :
    let b := y 1 + y 3
    let L := fderiv ℝ entranceWeakQuadratic y
    |entranceWeakQuadratic y| ≤ y 1 * b + 4 * y 3 ^ 2 / k ^ 2 ∧
    |L (Pi.single 0 1)| ≤ 32 * b ^ 2 / k ^ 3 ∧
    |L (Pi.single 1 1)| ≤ 2 * b ∧
    |L (Pi.single 3 1)| ≤ y 1 + 8 * y 3 / k ^ 2 := by
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hk0 : 0 < k := by linarith
  have hL0 : 0 < y 0 + 1 := by linarith
  have hL : k / 2 ≤ y 0 + 1 := by linarith [(entranceRegion_phase hk hy).1]
  have hu0 := hy.2.2.1.1
  have hw0 := hy.2.2.2.2.1
  have hi0 : 0 ≤ 1 / (y 0 + 1) ^ 2 := by positivity
  have hi1 : 1 / (y 0 + 1) ^ 2 ≤ 1 := (div_le_one (by positivity)).mpr (by nlinarith only [hm])
  have h40 : 0 ≤ 4 / (y 0 + 1) ^ 2 := by positivity
  have h41 : 4 / (y 0 + 1) ^ 2 ≤ 1 := (div_le_one (by positivity)).mpr (by nlinarith only [hm])
  have hA : |1 - 1 / (y 0 + 1) ^ 2| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hC : |-1 + 4 / (y 0 + 1) ^ 2| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hscale (q : ℝ) (hq : 0 ≤ q) (n : ℕ) : q / (y 0 + 1) ^ n ≤ 2 ^ n * q / k ^ n := by
    calc
      _ ≤ q / (k / 2) ^ n := div_le_div_of_nonneg_left hq (by positivity) (pow_le_pow_left₀ (by positivity) hL n)
      _ = _ := by simp only [div_pow]; field_simp
  have hd := (entranceWeakQuadratic_differential hL0.ne').2
  have h0 : fderiv ℝ entranceWeakQuadratic y (Pi.single 0 1) =
      (2 * y 1 ^ 2 - 8 * y 1 * y 3 + 2 * y 3 ^ 2) / (y 0 + 1) ^ 3 := by simp [hd]
  have h1 : fderiv ℝ entranceWeakQuadratic y (Pi.single 1 1) =
      2 * (1 - 1 / (y 0 + 1) ^ 2) * y 1 + (-1 + 4 / (y 0 + 1) ^ 2) * y 3 := by simp [hd]
  have h3 : fderiv ℝ entranceWeakQuadratic y (Pi.single 3 1) =
      (-1 + 4 / (y 0 + 1) ^ 2) * y 1 - 2 * y 3 / (y 0 + 1) ^ 2 := by simp [hd]
  dsimp only
  rw [h0, h1, h3]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold entranceWeakQuadratic
    calc
      _ ≤ |(1 - 1 / (y 0 + 1) ^ 2) * y 1 ^ 2| + |(-1 + 4 / (y 0 + 1) ^ 2) * y 1 * y 3| +
          |y 3 ^ 2 / (y 0 + 1) ^ 2| := (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ y 1 ^ 2 + y 1 * y 3 + 4 * y 3 ^ 2 / k ^ 2 := by
        simp only [abs_mul, abs_div, abs_of_nonneg hu0, abs_of_nonneg hw0,
          abs_of_nonneg (sq_nonneg (y 1)), abs_of_nonneg (sq_nonneg (y 3)), abs_of_nonneg (sq_nonneg (y 0 + 1))]
        exact add_le_add (add_le_add (by simpa using mul_le_mul_of_nonneg_right hA (sq_nonneg (y 1)))
          (by simpa using mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hu0) hw0))
          (by simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using hscale (y 3 ^ 2) (sq_nonneg _) 2)
      _ = _ := by ring
  · have hnum : |2 * y 1 ^ 2 - 8 * y 1 * y 3 + 2 * y 3 ^ 2| ≤ 4 * (y 1 + y 3) ^ 2 := by
      calc
        _ ≤ |2 * y 1 ^ 2| + |8 * y 1 * y 3| + |2 * y 3 ^ 2| :=
          (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
        _ = 2 * y 1 ^ 2 + 8 * y 1 * y 3 + 2 * y 3 ^ 2 := by
          rw [abs_of_nonneg (by positivity : 0 ≤ 2 * y 1 ^ 2), abs_of_nonneg (by positivity : 0 ≤ 8 * y 1 * y 3),
            abs_of_nonneg (by positivity : 0 ≤ 2 * y 3 ^ 2)]
        _ ≤ _ := by nlinarith only [sq_nonneg (y 1), sq_nonneg (y 3)]
    rw [abs_div, abs_of_pos (pow_pos hL0 3)]
    calc
      _ ≤ (4 * (y 1 + y 3) ^ 2) / (y 0 + 1) ^ 3 := div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ 2 ^ 3 * (4 * (y 1 + y 3) ^ 2) / k ^ 3 := hscale _ (by positivity) 3
      _ = _ := by ring
  · calc
      _ ≤ |2 * (1 - 1 / (y 0 + 1) ^ 2) * y 1| + |(-1 + 4 / (y 0 + 1) ^ 2) * y 3| := abs_add_le _ _
      _ ≤ 2 * y 1 + y 3 := by
        simp only [abs_mul, abs_of_nonneg hu0, abs_of_nonneg hw0]
        rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        exact add_le_add (by simpa using mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA (by norm_num : (0 : ℝ) ≤ 2)) hu0)
          (by simpa using mul_le_mul_of_nonneg_right hC hw0)
      _ ≤ _ := by linarith only [hw0]
  · calc
      _ ≤ |(-1 + 4 / (y 0 + 1) ^ 2) * y 1| + |2 * y 3 / (y 0 + 1) ^ 2| := abs_sub _ _
      _ ≤ y 1 + 8 * y 3 / k ^ 2 := by
        rw [abs_mul, abs_of_nonneg hu0, abs_of_nonneg (by positivity : 0 ≤ 2 * y 3 / (y 0 + 1) ^ 2)]
        exact add_le_add (by simpa using mul_le_mul_of_nonneg_right hC hu0)
          ((hscale (2 * y 3) (by positivity) 2).trans_eq (by ring))
