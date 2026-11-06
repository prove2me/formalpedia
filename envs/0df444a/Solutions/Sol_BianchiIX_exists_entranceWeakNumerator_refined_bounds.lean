-- Prove2me | solution 1 for BianchiIX.exists_entranceWeakNumerator_refined_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T17:01:05.652232+00:00
-- url     : https://prove2.me/submissions/6b999392-2417-4f53-949a-9426447b99d2

import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Definitions.Def_BianchiIX_StableProjectionRefinementData
import Definitions.Def_BianchiIX_Dynamics_EntranceRegion
import Definitions.Def_BianchiIX_EntrancePhaseResponseData
import Theorems.Thm_BianchiIX_contDiffAt_stableBoundaryProjection_two_in_band
import Theorems.Thm_BianchiIX_entranceWeakQuadratic_bounds
import Theorems.Thm_BianchiIX_entrance_phase_bounds
import Theorems.Thm_BianchiIX_exists_entranceWeakRemainder_bounds
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

private theorem BianchiIX.hasDerivAt_stableCorrectionA {m : ℝ} (hm : 1 < m) :
    HasDerivAt stableCorrectionA (-(m ^ 2 + 1) / (m ^ 2 - 1) ^ 2) m := by
  have hd : m ^ 2 - 1 ≠ 0 := by nlinarith
  convert! (hasDerivAt_id m).div (((hasDerivAt_id m).pow 2).sub_const 1) hd using 1
  dsimp
  congr 1
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_stableCorrectionC {m : ℝ} (hm : -1 < m) :
    HasDerivAt stableCorrectionC (2 / (m + 1) ^ 2) m := by
  have hd : m + 1 ≠ 0 := by linarith
  convert! (hasDerivAt_const m (-2 : ℝ)).div ((hasDerivAt_id m).add_const 1) hd using 1
  simp

end
end

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

private theorem BianchiIX.hasDerivAt_stableQuadraticPhase_phase {m u w : ℝ} (hm : 1 < m) :
    HasDerivAt (fun a => stableQuadraticPhase a u w)
      (1 + stableCorrectionADeriv m * u ^ 2 + stableCorrectionCDeriv m * u * w - w ^ 2 / (2 * (m + 1) ^ 2)) m := by
  have hden : 2 * (m + 1) ≠ 0 := by positivity
  have H := (((hasDerivAt_id m).add ((hasDerivAt_stableCorrectionA hm).mul_const (u ^ 2))).add
    (((hasDerivAt_stableCorrectionC (by linarith : -1 < m)).mul_const u).mul_const w)).add
    ((hasDerivAt_const m (w ^ 2)).div (((hasDerivAt_id m).add_const 1).const_mul 2) hden)
  apply H.congr_deriv
  dsimp [stableCorrectionADeriv, stableCorrectionCDeriv]
  have hL : m + 1 ≠ 0 := by linarith
  have hsq : m ^ 2 - 1 ≠ 0 := by nlinarith only [hm]
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entranceStablePartial_quadratic_phase {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) :
    entranceStablePartial y 0 = 1 + stableCorrectionADeriv (y 0) * y 1 ^ 2 +
      stableCorrectionCDeriv (y 0) * y 1 * y 3 - y 3 ^ 2 / (2 * (y 0 + 1) ^ 2) +
      fderiv ℝ entranceQuarticRemainder y (Pi.single 0 1) := by
  have hpath := hasDerivAt_update y 0 (y 0)
  have hR : HasFDerivAt entranceQuarticRemainder (fderiv ℝ entranceQuarticRemainder y) (Function.update y 0 (y 0)) := by
    simpa using ((contDiffAt_entranceQuarticRemainder_two hm hu hw).differentiableAt (by norm_num)).hasFDerivAt
  have hP : HasFDerivAt entranceStablePhase (fderiv ℝ entranceStablePhase y) (Function.update y 0 (y 0)) := by
    simpa using ((contDiffAt_entranceStablePhase_two hm hu hw).differentiableAt (by norm_num)).hasFDerivAt
  have hRP := hR.comp_hasDerivAt (y 0) hpath
  have hPQ := (hP.comp_hasDerivAt (y 0) hpath).sub
    (hasDerivAt_stableQuadraticPhase_phase (u := y 1) (w := y 3) (by linarith : 1 < y 0))
  have heq : (fun a => entranceQuarticRemainder (Function.update y 0 a)) =
      (fun a => entranceStablePhase (Function.update y 0 a) - stableQuadraticPhase a (y 1) (y 3)) := by
    funext a
    simp [entranceQuarticRemainder, stableQuadraticRemainder, entranceStablePhase, stableRestriction]
  change HasDerivAt (fun a => entranceQuarticRemainder (Function.update y 0 a)) _ (y 0) at hRP
  rw [heq] at hRP
  have H := hRP.unique hPQ
  dsimp [entranceStablePartial]
  linarith only [H]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entranceWeakNumerator_quadratic_expansion {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) :
    entranceWeakNumerator y = entranceWeakQuadratic y + entranceWeakRemainder y := by
  have hRM := entranceStablePartial_quadratic_phase hm hu hw
  have hR : entranceQuarticRemainder y = entranceStablePhase y - stableQuadraticPhase (y 0) (y 1) (y 3) := rfl
  have hd : y 0 + 1 ≠ 0 := by linarith
  have he : y 0 ^ 2 - 1 ≠ 0 := by nlinarith only [hm]
  unfold entranceWeakNumerator entranceWeakQuadratic entranceWeakRemainder
  rw [hR]
  have heq : fderiv ℝ entranceQuarticRemainder y (Pi.single 0 1) = entranceStablePartial y 0 -
      (1 + stableCorrectionADeriv (y 0) * y 1 ^ 2 + stableCorrectionCDeriv (y 0) * y 1 * y 3 - y 3 ^ 2 / (2 * (y 0 + 1) ^ 2)) := by
    linarith only [hRM]
  rw [heq]
  dsimp [stableQuadraticPhase, stableCorrectionA, stableCorrectionC, stableCorrectionADeriv, stableCorrectionCDeriv]
  field_simp
  ring

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

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.entranceWeakNumerator_expansion_fderiv {y : ProjectiveState}
    (hm : 2 < y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (v : ProjectiveState) :
    fderiv ℝ entranceWeakNumerator y v =
      fderiv ℝ entranceWeakQuadratic y v + fderiv ℝ entranceWeakRemainder y v := by
  have hm' : ∀ᶠ z : ProjectiveState in 𝓝 y, 2 < z 0 :=
    (continuousAt_apply 0 y).eventually (lt_mem_nhds hm)
  have hu' : ∀ᶠ z : ProjectiveState in 𝓝 y, |z 1| < 1 / 200 :=
    (continuousAt_apply 1 y).abs.eventually (gt_mem_nhds hu)
  have hw' : ∀ᶠ z : ProjectiveState in 𝓝 y, |z 3| < 1 / 200 :=
    (continuousAt_apply 3 y).abs.eventually (gt_mem_nhds hw)
  have heq : entranceWeakNumerator =ᶠ[𝓝 y] (fun z => entranceWeakQuadratic z + entranceWeakRemainder z) := by
    filter_upwards [hm', hu', hw'] with z hmz huz hwz
    exact entranceWeakNumerator_quadratic_expansion hmz.le huz hwz
  rw [heq.fderiv_eq, fderiv_fun_add (entranceWeakQuadratic_differential (by linarith)).1
    (entranceWeakRemainder_differential hm.le hu hw).1]
  rfl

end
end


set_option maxHeartbeats 500000 in
/-- The strengthened ordinary numerator bounds used by (C.23), including zero stable walls. -/
theorem solution :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y →
      k * (y 1 + y 3) ^ 2 ≤ 1 →
      let b := y 1 + y 3
      let L := fderiv ℝ entranceWeakNumerator y
      |entranceWeakNumerator y| ≤ C * (y 1 * b + y 3 ^ 2 / k ^ 2) ∧
      |L (Pi.single 0 1)| ≤ C * b ^ 2 / k ^ 3 ∧
      |L (Pi.single 1 1)| ≤ C * b ∧
      |L (Pi.single 3 1)| ≤ C * (y 1 + y 3 / k ^ 2) := by
  obtain ⟨R, hR, HR⟩ := exists_entranceWeakRemainder_bounds
  refine ⟨40 + 4 * R, by positivity, ?_⟩
  intro k y hk hy hsmall
  let b := y 1 + y 3
  have hb : 0 ≤ b := add_nonneg hy.2.2.1.1 hy.2.2.2.2.1
  have hb1 : b ≤ 1 := by dsimp [b]; linarith [hy.2.2.1.2, hy.2.2.2.2.2]
  have hu0 := hy.2.2.1.1
  have hw0 := hy.2.2.2.2.1
  have hk1 : 1 ≤ k := by linarith
  have hk0 : 0 < k := by linarith
  have hk2 : 1 ≤ k ^ 2 := one_le_pow₀ hk1
  have hm : 2 < y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hu0]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hw0]; linarith [hy.2.2.2.2.2]
  have hb2 : b ^ 2 ≤ 1 := by nlinarith only [hb, hb1]
  have hb3 : b ^ 3 ≤ b := by
    nlinarith only [mul_le_mul_of_nonneg_right hb2 hb]
  have hb4 : b ^ 4 ≤ b ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_right hb2 (sq_nonneg b)]
  have hquad : b ^ 2 ≤ 2 * y 1 * b + y 3 ^ 2 := by
    dsimp [b]
    nlinarith only [sq_nonneg (y 1)]
  have hvalscale : b ^ 4 / k ^ 2 ≤ 2 * y 1 * b + y 3 ^ 2 / k ^ 2 := by
    calc
      _ ≤ (2 * y 1 * b + y 3 ^ 2) / k ^ 2 := div_le_div_of_nonneg_right (hb4.trans hquad) (sq_nonneg k)
      _ = (2 * y 1 * b) / k ^ 2 + y 3 ^ 2 / k ^ 2 := by ring
      _ ≤ _ := add_le_add (div_le_self (by positivity) hk2) le_rfl
  have hphasescale : b ^ 4 / k ^ 2 ≤ b ^ 2 / k ^ 3 := by
    calc
      _ = (k * b ^ 2) * (b ^ 2 / k ^ 3) := by field_simp
      _ ≤ 1 * (b ^ 2 / k ^ 3) := mul_le_mul_of_nonneg_right hsmall (by positivity)
      _ = _ := one_mul _
  have hUscale : b ^ 3 / k ^ 2 ≤ b := (div_le_self (by positivity) hk2).trans hb3
  have hWscale : b ^ 3 / k ^ 2 ≤ y 1 + y 3 / k ^ 2 := by
    calc
      _ ≤ b / k ^ 2 := div_le_div_of_nonneg_right hb3 (sq_nonneg k)
      _ = y 1 / k ^ 2 + y 3 / k ^ 2 := by dsimp [b]; ring
      _ ≤ _ := add_le_add (div_le_self hu0 hk2) le_rfl
  obtain ⟨hphase, hwalls⟩ := HR k y hk hy
  have hE0 : |entranceWeakRemainder y| ≤ R * b ^ 4 / k ^ 2 := by
    linarith only [hphase, abs_nonneg (fderiv ℝ entranceWeakRemainder y (Pi.single 0 1))]
  have hEM : |fderiv ℝ entranceWeakRemainder y (Pi.single 0 1)| ≤ R * b ^ 4 / k ^ 2 := by
    linarith only [hphase, abs_nonneg (entranceWeakRemainder y)]
  have hEU : |fderiv ℝ entranceWeakRemainder y (Pi.single 1 1)| ≤ R * b ^ 3 / k ^ 2 := by
    linarith only [hwalls, abs_nonneg (fderiv ℝ entranceWeakRemainder y (Pi.single 3 1))]
  have hEW : |fderiv ℝ entranceWeakRemainder y (Pi.single 3 1)| ≤ R * b ^ 3 / k ^ 2 := by
    linarith only [hwalls, abs_nonneg (fderiv ℝ entranceWeakRemainder y (Pi.single 1 1))]
  have hmul (a c : ℝ) (ha : a ≤ c) : R * a ≤ R * c := mul_le_mul_of_nonneg_left ha hR.le
  have hE0' : |entranceWeakRemainder y| ≤ R * (2 * y 1 * b + y 3 ^ 2 / k ^ 2) :=
    hE0.trans ((by ring : R * b ^ 4 / k ^ 2 = R * (b ^ 4 / k ^ 2)).le.trans (hmul _ _ hvalscale))
  have hEM' : |fderiv ℝ entranceWeakRemainder y (Pi.single 0 1)| ≤ R * b ^ 2 / k ^ 3 := by
    calc
      _ ≤ R * b ^ 4 / k ^ 2 := hEM
      _ = R * (b ^ 4 / k ^ 2) := by ring
      _ ≤ R * (b ^ 2 / k ^ 3) := hmul _ _ hphasescale
      _ = _ := by ring
  have hEU' : |fderiv ℝ entranceWeakRemainder y (Pi.single 1 1)| ≤ R * b := by
    calc
      _ ≤ R * b ^ 3 / k ^ 2 := hEU
      _ = R * (b ^ 3 / k ^ 2) := by ring
      _ ≤ _ := hmul _ _ hUscale
  have hEW' : |fderiv ℝ entranceWeakRemainder y (Pi.single 3 1)| ≤ R * (y 1 + y 3 / k ^ 2) := by
    calc
      _ ≤ R * b ^ 3 / k ^ 2 := hEW
      _ = R * (b ^ 3 / k ^ 2) := by ring
      _ ≤ _ := hmul _ _ hWscale
  obtain ⟨hQ, hQM, hQU, hQW⟩ := entranceWeakQuadratic_bounds hk hy
  have hd := entranceWeakNumerator_expansion_fderiv hm hu hw
  dsimp only
  rw [entranceWeakNumerator_quadratic_expansion hm.le hu hw, hd, hd, hd]
  refine ⟨((abs_add_le _ _).trans (add_le_add hQ hE0')).trans ?_,
    ((abs_add_le _ _).trans (add_le_add hQM hEM')).trans ?_,
    ((abs_add_le _ _).trans (add_le_add hQU hEU')).trans ?_,
    ((abs_add_le _ _).trans (add_le_add hQW hEW')).trans ?_⟩
  · change y 1 * b + 4 * y 3 ^ 2 / k ^ 2 + R * (2 * y 1 * b + y 3 ^ 2 / k ^ 2) ≤ _
    have hUb : 0 ≤ y 1 * b := mul_nonneg hu0 hb
    have htail : 0 ≤ y 3 ^ 2 / k ^ 2 := by positivity
    have hc (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) : a + 4 * c + R * (2 * a + c) ≤ (40 + 4 * R) * (a + c) := by
      nlinarith only [ha, hc, mul_nonneg hR.le ha, mul_nonneg hR.le hc]
    convert! hc _ _ hUb htail using 1
    ring
  · calc
      _ = (32 + R) * b ^ 2 / k ^ 3 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith only [hR]) (sq_nonneg b)) (by positivity)
  · change 2 * b + R * b ≤ _
    nlinarith only [hb, mul_nonneg hR.le hb]
  · change y 1 + 8 * y 3 / k ^ 2 + R * (y 1 + y 3 / k ^ 2) ≤ _
    have htail : 0 ≤ y 3 / k ^ 2 := by positivity
    have hc (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) : a + 8 * c + R * (a + c) ≤ (40 + 4 * R) * (a + c) := by
      nlinarith only [ha, hc, mul_nonneg hR.le ha, mul_nonneg hR.le hc]
    convert! hc _ _ hu0 htail using 1
    ring
