-- Prove2me | solution 1 for BianchiIX.exists_entranceWeakRemainder_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T16:57:05.080837+00:00
-- url     : https://prove2.me/submissions/91cfb97c-6e97-461d-bfa3-ba7582a31d19

import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Definitions.Def_BianchiIX_StableProjectionRefinementData
import Definitions.Def_BianchiIX_Dynamics_EntranceRegion
import Definitions.Def_BianchiIX_EntrancePhaseResponseData
import Theorems.Thm_BianchiIX_contDiffAt_stableBoundaryProjection_two_in_band
import Theorems.Thm_BianchiIX_entrance_phase_bounds
import Theorems.Thm_BianchiIX_exists_entranceProjection_estimates
import Theorems.Thm_BianchiIX_exists_stableQuadraticRemainder_bounds
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

private theorem BianchiIX.contDiffAt_stableCorrectedPhase (n : WithTop ℕ∞) {y : Fin 3 → ℝ}
    (hm : 1 < y 0) :
    ContDiffAt ℝ n (fun z : Fin 3 → ℝ => stableCorrectedPhase (z 0) (z 1) (z 2)) y := by
  have hL : y 0 + 1 ≠ 0 := by linarith
  have hD : y 0 ^ 2 - 1 ≠ 0 := by nlinarith
  have hS : (y 0 + 1) ^ 2 + y 2 ^ 2 ≠ 0 := by
    have h : 0 < y 0 + 1 := by linarith
    positivity
  unfold stableCorrectedPhase stableWeakRadius phaseNorm stableCorrectionA stableCorrectionC
  fun_prop

end
end

section
noncomputable section
open BianchiIX
open scoped Topology

private theorem BianchiIX.contDiffAt_stableWeakRemainder (n : WithTop ℕ∞) {y : Fin 3 → ℝ} (hm : -1 < y 0) :
    ContDiffAt ℝ n (fun z : Fin 3 → ℝ => stableWeakRemainder (z 0) (z 2)) y := by
  have hL : y 0 + 1 ≠ 0 := by linarith
  have h2L : 2 * (y 0 + 1) ≠ 0 := mul_ne_zero (by norm_num) hL
  have hS : (y 0 + 1) ^ 2 + y 2 ^ 2 ≠ 0 := by
    have h : 0 < y 0 + 1 := by linarith
    positivity
  unfold stableWeakRemainder stableWeakRadius phaseNorm
  fun_prop

end
end

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

private theorem BianchiIX.stableRestriction_apply (y : ProjectiveState) : stableRestriction y = ![y 0, y 1, y 3] := by
  ext i
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_stableBoundaryProjection_two {y : StableState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) :
    ContDiffAt ℝ 2 (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)) y :=
  contDiffAt_stableBoundaryProjection_two_in_band hm (by simp) hu hw

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_entranceStablePhase_two {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) :
    ContDiffAt ℝ 2 entranceStablePhase y :=
  (contDiffAt_stableBoundaryProjection_two (y := stableRestriction y) hm hu hw).comp y
    stableRestriction.contDiff.contDiffAt

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

attribute [local instance] BianchiIX.stableQuadraticExpansionOperatorGroup
attribute [local instance] BianchiIX.stableQuadraticExpansionOperatorSpace
private theorem BianchiIX.stableQuadraticRemainder_decomposition :
    stableQuadraticRemainder = fun y => stableCorrectedRemainder y + stableWeakRemainder (y 0) (y 2) := by
  funext y
  unfold stableQuadraticRemainder stableQuadraticPhase stableCorrectedRemainder stableCorrectedPhase stableWeakRemainder
  ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

attribute [local instance] BianchiIX.stableQuadraticExpansionOperatorGroup
attribute [local instance] BianchiIX.stableQuadraticExpansionOperatorSpace
private theorem BianchiIX.stableQuadraticRemainder_derivatives {y : StableState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) :
    let E := fun z : StableState => stableWeakRemainder (z 0) (z 2)
    ContDiffAt ℝ 2 stableQuadraticRemainder y ∧
      fderiv ℝ stableQuadraticRemainder y = fderiv ℝ stableCorrectedRemainder y + fderiv ℝ E y ∧
      fderiv ℝ (fderiv ℝ stableQuadraticRemainder) y =
        fderiv ℝ (fderiv ℝ stableCorrectedRemainder) y + fderiv ℝ (fderiv ℝ E) y := by
  have hR : ContDiffAt ℝ 2 stableCorrectedRemainder y :=
    (contDiffAt_stableBoundaryProjection_two hm hu hw).sub (contDiffAt_stableCorrectedPhase 2 (by linarith))
  have hE := contDiffAt_stableWeakRemainder 2 (y := y) (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · rw [stableQuadraticRemainder_decomposition]
    exact hR.add hE
  · rw [stableQuadraticRemainder_decomposition]
    exact fderiv_fun_add (hR.differentiableAt (by norm_num)) (hE.differentiableAt (by norm_num))
  · have heq : fderiv ℝ stableQuadraticRemainder =ᶠ[𝓝 y] (fun z => fderiv ℝ stableCorrectedRemainder z +
        fderiv ℝ (fun a : StableState => stableWeakRemainder (a 0) (a 2)) z) := by
      filter_upwards [hR.eventually (by norm_num), hE.eventually (by norm_num)] with z hr he
      rw [stableQuadraticRemainder_decomposition]
      exact fderiv_fun_add (hr.differentiableAt (by norm_num)) (he.differentiableAt (by norm_num))
    rw [heq.fderiv_eq]
    exact fderiv_fun_add
      ((hR.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num))
      ((hE.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num))

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

local instance  : NormedAddCommGroup (ProjectiveState →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance  : NormedSpace ℝ (ProjectiveState →L[ℝ] ℝ) := inferInstance
attribute [local instance] BianchiIX.entranceQuarticStableOperatorGroup
attribute [local instance] BianchiIX.entranceQuarticStableOperatorSpace
private theorem BianchiIX.contDiffAt_entranceQuarticRemainder_two {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) :
    ContDiffAt ℝ 2 entranceQuarticRemainder y :=
  (stableQuadraticRemainder_derivatives (y := stableRestriction y) hm hu hw).1.comp y stableRestriction.contDiff.contDiffAt

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

local instance  : NormedAddCommGroup (ProjectiveState →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance  : NormedSpace ℝ (ProjectiveState →L[ℝ] ℝ) := inferInstance
attribute [local instance] BianchiIX.entranceQuarticStableOperatorGroup
attribute [local instance] BianchiIX.entranceQuarticStableOperatorSpace
private theorem BianchiIX.entranceQuarticRemainder_fderiv {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (v : ProjectiveState) :
    fderiv ℝ entranceQuarticRemainder y v =
      fderiv ℝ stableQuadraticRemainder (stableRestriction y) (stableRestriction v) := by
  have H := ((stableQuadraticRemainder_derivatives (y := stableRestriction y) hm hu hw).1.differentiableAt
    (by norm_num)).hasFDerivAt.comp y stableRestriction.hasFDerivAt
  exact congrArg (fun L : ProjectiveState →L[ℝ] ℝ => L v) H.fderiv

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

local instance  : NormedAddCommGroup (ProjectiveState →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance  : NormedSpace ℝ (ProjectiveState →L[ℝ] ℝ) := inferInstance
attribute [local instance] BianchiIX.entranceQuarticStableOperatorGroup
attribute [local instance] BianchiIX.entranceQuarticStableOperatorSpace
private theorem BianchiIX.entranceQuarticRemainder_hessian {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (v w : ProjectiveState) :
    fderiv ℝ (fderiv ℝ entranceQuarticRemainder) y v w =
      fderiv ℝ (fderiv ℝ stableQuadraticRemainder) (stableRestriction y) (stableRestriction v) (stableRestriction w) := by
  have hR := (stableQuadraticRemainder_derivatives (y := stableRestriction y) hm hu hw).1
  have heq : (fun z => fderiv ℝ entranceQuarticRemainder z w) =ᶠ[𝓝 y]
      (fun z => fderiv ℝ stableQuadraticRemainder (stableRestriction z) (stableRestriction w)) := by
    filter_upwards [stableRestriction.continuous.continuousAt.eventually (hR.eventually (by norm_num))] with z hz
    have H := (hz.differentiableAt (by norm_num)).hasFDerivAt.comp z stableRestriction.hasFDerivAt
    exact congrArg (fun L : ProjectiveState →L[ℝ] ℝ => L w) H.fderiv
  have hleft := (((contDiffAt_entranceQuarticRemainder_two hm hu hw).fderiv_right
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)).hasFDerivAt.clm_apply
      (hasFDerivAt_const (𝕜 := ℝ) w y)
  have hright := (((hR.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt
    (by norm_num)).hasFDerivAt.comp y stableRestriction.hasFDerivAt).clm_apply
      (hasFDerivAt_const (𝕜 := ℝ) (stableRestriction w) y)
  have H := congrArg (fun L : ProjectiveState →L[ℝ] ℝ => L v) heq.fderiv_eq
  change HasFDerivAt (fun z => fderiv ℝ stableQuadraticRemainder (stableRestriction z) (stableRestriction w)) _ y at hright
  rw [hleft.fderiv, hright.fderiv] at H
  simpa using H

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

local instance  : NormedAddCommGroup (ProjectiveState →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance  : NormedSpace ℝ (ProjectiveState →L[ℝ] ℝ) := inferInstance
attribute [local instance] BianchiIX.entranceQuarticStableOperatorGroup
attribute [local instance] BianchiIX.entranceQuarticStableOperatorSpace
private theorem BianchiIX.exists_entranceQuarticRemainder_bounds :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y →
      let b := y 1 + y 3
      let L := fderiv ℝ entranceQuarticRemainder y
      let Q := fderiv ℝ (fderiv ℝ entranceQuarticRemainder) y
      |entranceQuarticRemainder y| ≤ C * b ^ 4 / k ^ 3 ∧
      |L (Pi.single 0 1)| ≤ C * b ^ 4 / k ^ 3 ∧
      |L (Pi.single 1 1)| ≤ C * b ^ 3 / k ^ 3 ∧
      |L (Pi.single 3 1)| ≤ C * b ^ 3 / k ^ 3 ∧
      |Q (Pi.single 0 1) (Pi.single 0 1)| ≤ C * b ^ 4 / k ^ 3 ∧
      |Q (Pi.single 1 1) (Pi.single 0 1)| ≤ C * b ^ 3 / k ^ 3 ∧
      |Q (Pi.single 3 1) (Pi.single 0 1)| ≤ C * b ^ 3 / k ^ 3 := by
  obtain ⟨C, hC, HC⟩ := exists_stableQuadraticRemainder_bounds
  refine ⟨8 * C, by positivity, ?_⟩
  intro k y hk hy
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  have hk0 : 0 < k := by linarith
  have hL : k / 2 ≤ y 0 + 1 := by linarith [(entranceRegion_phase hk hy).1]
  have hb : 0 ≤ y 1 + y 3 := add_nonneg hy.2.2.1.1 hy.2.2.2.2.1
  have hscale (q : ℝ) (hq : 0 ≤ q) : C / (y 0 + 1) ^ 3 * q ≤ 8 * C * q / k ^ 3 := by
    calc
      _ ≤ C / (k / 2) ^ 3 * q := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left hC.le (by positivity) (pow_le_pow_left₀ (by positivity) hL 3)) hq
      _ = _ := by field_simp; ring
  have h0 : stableRestriction (Pi.single (0 : Fin 4) (1 : ℝ)) = Pi.single 0 1 := by
    ext i; fin_cases i <;> simp [stableRestriction]
  have h1 : stableRestriction (Pi.single (1 : Fin 4) (1 : ℝ)) = Pi.single 1 1 := by
    ext i; fin_cases i <;> simp [stableRestriction]
  have h3 : stableRestriction (Pi.single (3 : Fin 4) (1 : ℝ)) = Pi.single 2 1 := by
    ext i; fin_cases i <;> simp [stableRestriction]
  obtain ⟨_, Hval, hM, hz, hMM, hMz, _⟩ := HC (stableRestriction y) hm hu hw
  have H0 := hM (Pi.single 0 1) (by simp) (by simp)
  have H1 := hz (Pi.single 1 1) (by simp)
  have H3 := hz (Pi.single 2 1) (by simp)
  have H00 := hMM (Pi.single 0 1) (Pi.single 0 1) (by simp) (by simp) (by simp) (by simp)
  have H01 := hMz (Pi.single 0 1) (Pi.single 1 1) (by simp) (by simp) (by simp)
  have H03 := hMz (Pi.single 0 1) (Pi.single 2 1) (by simp) (by simp) (by simp)
  have hsym := (contDiffAt_entranceQuarticRemainder_two hm hu hw).isSymmSndFDerivAt (by norm_num)
  dsimp only
  rw [hsym.eq (Pi.single 1 1) (Pi.single 0 1), hsym.eq (Pi.single 3 1) (Pi.single 0 1)]
  simp only [entranceQuarticRemainder_fderiv hm hu hw, entranceQuarticRemainder_hessian hm hu hw, h0, h1, h3]
  simp only [entranceQuarticRemainder, stableRestriction_apply]
  simp only [stableRestriction_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Pi.norm_single, norm_one, mul_one, abs_of_nonneg hy.2.2.1.1, abs_of_nonneg hy.2.2.2.2.1] at Hval H0 H1 H3 H00 H01 H03
  exact ⟨Hval.trans (hscale _ (by positivity)), H0.trans (hscale _ (by positivity)),
    H1.trans (hscale _ (by positivity)), H3.trans (hscale _ (by positivity)),
    H00.trans (hscale _ (by positivity)), H01.trans (hscale _ (by positivity)), H03.trans (hscale _ (by positivity))⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entranceWeakRemainder_differential {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) :
    DifferentiableAt ℝ entranceWeakRemainder y ∧ ∀ v : ProjectiveState,
      fderiv ℝ entranceWeakRemainder y v =
        -fderiv ℝ entranceQuarticRemainder y v - v 0 * fderiv ℝ entranceQuarticRemainder y (Pi.single 0 1) -
        (y 0 - 1) * fderiv ℝ (fderiv ℝ entranceQuarticRemainder) y v (Pi.single 0 1) -
        (fderiv ℝ entranceStablePhase y v - v 0) * (entranceStablePartial y 0 - 1) -
        (entranceStablePhase y - y 0) * fderiv ℝ (fderiv ℝ entranceStablePhase) y v (Pi.single 0 1) := by
  have hR := contDiffAt_entranceQuarticRemainder_two hm hu hw
  have hRM := (((hR.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt
    (by norm_num)).hasFDerivAt).clm_apply (hasFDerivAt_const (𝕜 := ℝ) (Pi.single 0 1) y)
  have hP := contDiffAt_entranceStablePhase_two hm hu hw
  have hPM := (((hP.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt
    (by norm_num)).hasFDerivAt).clm_apply (hasFDerivAt_const (𝕜 := ℝ) (Pi.single 0 1) y)
  have hd := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) y
  have hfirst := ((hR.differentiableAt (by norm_num)).hasFDerivAt.neg).sub ((hd.sub_const 1).mul hRM)
  have H := hfirst.sub
    ((((hP.differentiableAt (by norm_num)).hasFDerivAt).sub hd).mul (hPM.sub_const 1))
  change HasFDerivAt entranceWeakRemainder _ y at H
  refine ⟨H.differentiableAt, fun v => ?_⟩
  rw [H.fderiv]
  simp [entranceStablePartial, sub_apply, add_apply, neg_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, Pi.sub_apply]
  ring

end
end


set_option maxHeartbeats 600000 in
/-- The nonlinear error in the weak numerator has fourth amplitude order, including its phase derivative. -/
theorem solution :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y →
      let b := y 1 + y 3
      let L := fderiv ℝ entranceWeakRemainder y
      |entranceWeakRemainder y| + |L (Pi.single 0 1)| ≤ C * b ^ 4 / k ^ 2 ∧
      |L (Pi.single 1 1)| + |L (Pi.single 3 1)| ≤ C * b ^ 3 / k ^ 2 := by
  obtain ⟨R, hR, HR⟩ := exists_entranceQuarticRemainder_bounds
  obtain ⟨P, hP, HP⟩ := exists_entranceProjection_estimates
  refine ⟨10 * (R + P ^ 2 + 1), by positivity, ?_⟩
  intro k y hk hy
  let b := y 1 + y 3
  have hb : 0 ≤ b := add_nonneg hy.2.2.1.1 hy.2.2.2.2.1
  have hk1 : 1 ≤ k := by linarith
  have hk0 : 0 < k := by linarith
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hm0 : 0 ≤ y 0 - 1 := by linarith
  have hm2 : y 0 - 1 ≤ 2 * k := by linarith [(entranceRegion_phase hk hy).2]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  obtain ⟨hval, hM, hU, hW, hMM, hMU, hMW⟩ := HR k y hk hy
  obtain ⟨hQ, hQM, hQU, hQW, hQMM, hQMU, hQMW⟩ := HP k y hk hy
  have hscale (a : ℝ) (ha : 0 ≤ a) (n : ℕ) (hn : 2 ≤ n) : a / k ^ n ≤ a / k ^ 2 :=
    div_le_div_of_nonneg_left ha (by positivity) (pow_le_pow_right₀ hk1 hn)
  have hphase (a : ℝ) (n : ℕ) (ha : |a| ≤ R * b ^ n / k ^ 3) :
      |(y 0 - 1) * a| ≤ 2 * R * b ^ n / k ^ 2 := by
    rw [abs_mul, abs_of_nonneg hm0]
    calc
      _ ≤ (2 * k) * (R * b ^ n / k ^ 3) := mul_le_mul hm2 ha (abs_nonneg _) (by positivity)
      _ = _ := by field_simp
  have hproduct (a c : ℝ) (p q n m : ℕ) (hn : 2 ≤ n + m)
      (ha : |a| ≤ P * b ^ p / k ^ n) (hc : |c| ≤ P * b ^ q / k ^ m) :
      |a * c| ≤ P ^ 2 * b ^ (p + q) / k ^ 2 := by
    rw [abs_mul]
    calc
      _ ≤ (P * b ^ p / k ^ n) * (P * b ^ q / k ^ m) := mul_le_mul ha hc (abs_nonneg _) (by positivity)
      _ = P ^ 2 * b ^ (p + q) / k ^ (n + m) := by rw [pow_add, pow_add]; ring
      _ ≤ _ := hscale _ (by positivity) _ hn
  have hQ' : |entranceStablePhase y - y 0| ≤ P * b ^ 2 / k ^ 1 := by simpa using hQ
  have hprod0 := hproduct _ _ 2 2 1 2 (by norm_num) hQ' hQM
  have hprod1 := hproduct _ _ 2 2 2 2 (by norm_num) hQM hQM
  have hprod2 := hproduct _ _ 2 2 1 3 (by norm_num) hQ' hQMM
  have hneg3 (a c d : ℝ) : |-a - c - d| ≤ |a| + |c| + |d| := by
    simpa only [abs_neg] using (abs_sub (-a - c) d).trans (add_le_add (abs_sub (-a) c) le_rfl)
  have hE : |entranceWeakRemainder y| ≤ (3 * R + P ^ 2) * b ^ 4 / k ^ 2 := by
    unfold entranceWeakRemainder
    calc
      _ ≤ |entranceQuarticRemainder y| + |(y 0 - 1) * fderiv ℝ entranceQuarticRemainder y (Pi.single 0 1)| +
          |(entranceStablePhase y - y 0) * (entranceStablePartial y 0 - 1)| := hneg3 _ _ _
      _ ≤ R * b ^ 4 / k ^ 2 + 2 * R * b ^ 4 / k ^ 2 + P ^ 2 * b ^ 4 / k ^ 2 :=
        add_le_add (add_le_add (hval.trans (hscale _ (by positivity) 3 (by norm_num))) (hphase _ 4 hM)) hprod0
      _ = _ := by ring
  have hd := (entranceWeakRemainder_differential hm hu hw).2
  have hEM : |fderiv ℝ entranceWeakRemainder y (Pi.single 0 1)| ≤ (4 * R + 2 * P ^ 2) * b ^ 4 / k ^ 2 := by
    have heq : fderiv ℝ entranceWeakRemainder y (Pi.single 0 1) =
        -fderiv ℝ entranceQuarticRemainder y (Pi.single 0 1) - fderiv ℝ entranceQuarticRemainder y (Pi.single 0 1) -
        (y 0 - 1) * fderiv ℝ (fderiv ℝ entranceQuarticRemainder) y (Pi.single 0 1) (Pi.single 0 1) -
        (entranceStablePartial y 0 - 1) * (entranceStablePartial y 0 - 1) -
        (entranceStablePhase y - y 0) * fderiv ℝ (fderiv ℝ entranceStablePhase) y (Pi.single 0 1) (Pi.single 0 1) := by
      rw [hd]
      simp [entranceStablePartial]
    rw [heq]
    calc
      _ ≤ |fderiv ℝ entranceQuarticRemainder y (Pi.single 0 1)| + |fderiv ℝ entranceQuarticRemainder y (Pi.single 0 1)| +
          |(y 0 - 1) * fderiv ℝ (fderiv ℝ entranceQuarticRemainder) y (Pi.single 0 1) (Pi.single 0 1)| +
          |(entranceStablePartial y 0 - 1) * (entranceStablePartial y 0 - 1)| +
          |(entranceStablePhase y - y 0) * fderiv ℝ (fderiv ℝ entranceStablePhase) y (Pi.single 0 1) (Pi.single 0 1)| := by
        refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
        exact (abs_sub _ _).trans (add_le_add (hneg3 _ _ _) le_rfl)
      _ ≤ R * b ^ 4 / k ^ 2 + R * b ^ 4 / k ^ 2 + 2 * R * b ^ 4 / k ^ 2 +
          P ^ 2 * b ^ 4 / k ^ 2 + P ^ 2 * b ^ 4 / k ^ 2 :=
        add_le_add (add_le_add (add_le_add (add_le_add (hM.trans (hscale _ (by positivity) 3 (by norm_num)))
          (hM.trans (hscale _ (by positivity) 3 (by norm_num)))) (hphase _ 4 hMM)) hprod1) hprod2
      _ = _ := by ring
  have hwall (i : Fin 4) (hi : i ≠ 0)
      (hRi : |fderiv ℝ entranceQuarticRemainder y (Pi.single i 1)| ≤ R * b ^ 3 / k ^ 3)
      (hRMi : |fderiv ℝ (fderiv ℝ entranceQuarticRemainder) y (Pi.single i 1) (Pi.single 0 1)| ≤ R * b ^ 3 / k ^ 3)
      (hPi : |entranceStablePartial y i| ≤ P * b / k)
      (hPMi : |fderiv ℝ (fderiv ℝ entranceStablePhase) y (Pi.single i 1) (Pi.single 0 1)| ≤ P * b / k ^ 2) :
      |fderiv ℝ entranceWeakRemainder y (Pi.single i 1)| ≤ (3 * R + 2 * P ^ 2) * b ^ 3 / k ^ 2 := by
    have heq : fderiv ℝ entranceWeakRemainder y (Pi.single i 1) =
        -fderiv ℝ entranceQuarticRemainder y (Pi.single i 1) -
        (y 0 - 1) * fderiv ℝ (fderiv ℝ entranceQuarticRemainder) y (Pi.single i 1) (Pi.single 0 1) -
        entranceStablePartial y i * (entranceStablePartial y 0 - 1) -
        (entranceStablePhase y - y 0) * fderiv ℝ (fderiv ℝ entranceStablePhase) y (Pi.single i 1) (Pi.single 0 1) := by
      rw [hd]
      simp [entranceStablePartial, Ne.symm hi]
    have hpi' : |entranceStablePartial y i| ≤ P * b ^ 1 / k ^ 1 := by simpa using hPi
    have hpmi' : |fderiv ℝ (fderiv ℝ entranceStablePhase) y (Pi.single i 1) (Pi.single 0 1)| ≤ P * b ^ 1 / k ^ 2 := by simpa using hPMi
    have hp1 := hproduct _ _ 1 2 1 2 (by norm_num) hpi' hQM
    have hp2 := hproduct _ _ 2 1 1 2 (by norm_num) hQ' hpmi'
    rw [heq]
    calc
      _ ≤ |fderiv ℝ entranceQuarticRemainder y (Pi.single i 1)| +
          |(y 0 - 1) * fderiv ℝ (fderiv ℝ entranceQuarticRemainder) y (Pi.single i 1) (Pi.single 0 1)| +
          |entranceStablePartial y i * (entranceStablePartial y 0 - 1)| +
          |(entranceStablePhase y - y 0) * fderiv ℝ (fderiv ℝ entranceStablePhase) y (Pi.single i 1) (Pi.single 0 1)| := by
        exact (abs_sub _ _).trans (add_le_add (hneg3 _ _ _) le_rfl)
      _ ≤ R * b ^ 3 / k ^ 2 + 2 * R * b ^ 3 / k ^ 2 + P ^ 2 * b ^ 3 / k ^ 2 + P ^ 2 * b ^ 3 / k ^ 2 :=
        add_le_add (add_le_add (add_le_add (hRi.trans (hscale _ (by positivity) 3 (by norm_num))) (hphase _ 3 hRMi)) hp1) hp2
      _ = _ := by ring
  have hEU := hwall 1 (by decide) hU hMU hQU hQMU
  have hEW := hwall 3 (by decide) hW hMW hQW hQMW
  constructor
  · calc
      _ ≤ (3 * R + P ^ 2) * b ^ 4 / k ^ 2 + (4 * R + 2 * P ^ 2) * b ^ 4 / k ^ 2 := add_le_add hE hEM
      _ = (7 * R + 3 * P ^ 2) * b ^ 4 / k ^ 2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by nlinarith only [hR, sq_nonneg P]) (by positivity)) (sq_nonneg k)
  · calc
      _ ≤ (3 * R + 2 * P ^ 2) * b ^ 3 / k ^ 2 + (3 * R + 2 * P ^ 2) * b ^ 3 / k ^ 2 := add_le_add hEU hEW
      _ = (6 * R + 4 * P ^ 2) * b ^ 3 / k ^ 2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by nlinarith only [hR, sq_nonneg P]) (by positivity)) (sq_nonneg k)
