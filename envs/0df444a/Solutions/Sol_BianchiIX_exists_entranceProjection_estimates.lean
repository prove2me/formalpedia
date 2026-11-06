-- Prove2me | solution 1 for BianchiIX.exists_entranceProjection_estimates
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T16:54:39.382395+00:00
-- url     : https://prove2.me/submissions/eec9fb3b-2d1e-4e5a-a302-3da277eff20b

import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Definitions.Def_BianchiIX_Dynamics_EntranceRegion
import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Definitions.Def_BianchiIX_EntrancePhaseResponseData
import Theorems.Thm_BianchiIX_contDiffAt_stableBoundaryProjection_two_in_band
import Theorems.Thm_BianchiIX_entrance_phase_bounds
import Theorems.Thm_BianchiIX_exists_stableBoundaryProjection_refined_derivatives
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_normalized_stable_limit
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
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
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
open BianchiIX
open Filter
open scoped Topology

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
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.stableBoundaryEntry_denom_pos (m u w : ℝ) :
    0 < projectiveStateDenom (stableBoundaryEntry m u w) := by
  change 0 < projectiveDenom m u 0 w
  have H : projectiveDenom m u 0 w = 3 + m ^ 2 + (u - w) ^ 2 := by
    unfold projectiveDenom curvature
    ring
  rw [H]
  positivity

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.stableBoundaryOrbit_initial (m u w : ℝ) :
    stableBoundaryOrbit m u w 0 = stableBoundaryEntry m u w := by
  unfold stableBoundaryOrbit
  rw [normalizedMaxCurve_initial]
  exact toProjectiveState_fromProjectiveState (ne_of_gt (stableBoundaryEntry_denom_pos m u w))

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.stableBoundaryProjection_exists {m c u w : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40)
    (hu : |u| ≤ 1 / 200) (hw : |w| ≤ 1 / 200) :
    Tendsto (fun t => stableBoundaryOrbit m u w t 0) atTop (𝓝 (stableBoundaryProjection m u w)) ∧
    Tendsto (fun t => stableBoundaryOrbit m u w t 1) atTop (𝓝 0) ∧
    Tendsto (fun t => stableBoundaryOrbit m u w t 3) atTop (𝓝 0) ∧
    (∀ t ≥ 0, |stableBoundaryProjection m u w - stableBoundaryOrbit m u w t 0| ≤
      8 * (|stableBoundaryOrbit m u w t 1| + |stableBoundaryOrbit m u w t 3|) ^ 2 / (c + 1)) ∧
    |stableBoundaryProjection m u w - m| ≤ 8 * (|u| + |w|) ^ 2 / (c + 1) := by
  let x := fromProjectiveState (stableBoundaryEntry m u w)
  have hD := stableBoundaryEntry_denom_pos m u w
  have hx : stateConstraint x = 1 := fromProjectiveState_constraint (ne_of_gt hD)
  have hA : 0 < normalizedProjectiveRate x 0 0 := by
    unfold normalizedProjectiveRate
    rw [normalizedMaxCurve_initial]
    exact fromProjectiveState_clock_pos hD
  have hi := stableBoundaryOrbit_initial m u w
  have H := normalized_stable_limit hx hc (le_refl 0) hA
  change |stableBoundaryOrbit m u w 0 0 - c| ≤ 1 / 40 →
    |stableBoundaryOrbit m u w 0 1| ≤ 1 / 200 → stableBoundaryOrbit m u w 0 2 = 0 →
    |stableBoundaryOrbit m u w 0 3| ≤ 1 / 200 → _ at H
  obtain ⟨P, hP, hU, hW, htail⟩ := H (by simpa [hi, stableBoundaryEntry] using hm)
    (by simpa [hi, stableBoundaryEntry] using hu) (by simp [hi, stableBoundaryEntry])
    (by simpa [hi, stableBoundaryEntry] using hw)
  have heq : stableBoundaryProjection m u w = P := hP.limUnder_eq
  rw [heq]
  refine ⟨hP, hU, hW, htail, ?_⟩
  have H0 := htail 0 le_rfl
  change |P - stableBoundaryOrbit m u w 0 0| ≤
    8 * (|stableBoundaryOrbit m u w 0 1| + |stableBoundaryOrbit m u w 0 3|) ^ 2 / (c + 1) at H0
  simpa [hi, stableBoundaryEntry] using H0

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

private theorem BianchiIX.entranceStablePhase_fderiv {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (v : ProjectiveState) :
    fderiv ℝ entranceStablePhase y v =
      fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2))
        (stableRestriction y) (stableRestriction v) := by
  have H := ((contDiffAt_stableBoundaryProjection_two (y := stableRestriction y) hm hu hw).differentiableAt
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
attribute [local instance] BianchiIX.entranceStableOperatorGroup
attribute [local instance] BianchiIX.entranceStableOperatorSpace
private theorem BianchiIX.entranceStablePhase_hessian {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (v w : ProjectiveState) :
    fderiv ℝ (fderiv ℝ entranceStablePhase) y v w =
      fderiv ℝ (fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)))
        (stableRestriction y) (stableRestriction v) (stableRestriction w) := by
  let P := fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)
  have hP : ContDiffAt ℝ 2 P (stableRestriction y) := contDiffAt_stableBoundaryProjection_two hm hu hw
  have heq : (fun z => fderiv ℝ entranceStablePhase z w) =ᶠ[𝓝 y]
      (fun z => fderiv ℝ P (stableRestriction z) (stableRestriction w)) := by
    filter_upwards [stableRestriction.continuous.continuousAt.eventually (hP.eventually (by norm_num))] with z hz
    have H := (hz.differentiableAt (by norm_num)).hasFDerivAt.comp z stableRestriction.hasFDerivAt
    exact congrArg (fun L : ProjectiveState →L[ℝ] ℝ => L w) H.fderiv
  have hL := (((contDiffAt_entranceStablePhase_two hm hu hw).fderiv_right
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)).hasFDerivAt.clm_apply
      (hasFDerivAt_const (𝕜 := ℝ) w y)
  have hR := (((hP.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt
    (by norm_num)).hasFDerivAt.comp y stableRestriction.hasFDerivAt).clm_apply
      (hasFDerivAt_const (𝕜 := ℝ) (stableRestriction w) y)
  have H := congrArg (fun L : ProjectiveState →L[ℝ] ℝ => L v) heq.fderiv_eq
  change HasFDerivAt (fun z => fderiv ℝ P (stableRestriction z) (stableRestriction w)) _ y at hR
  rw [hL.fderiv, hR.fderiv] at H
  simpa [P] using H

end
end

local instance  : NormedAddCommGroup (ProjectiveState →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance  : NormedSpace ℝ (ProjectiveState →L[ℝ] ℝ) := inferInstance
attribute [local instance] BianchiIX.entranceStableOperatorGroup
attribute [local instance] BianchiIX.entranceStableOperatorSpace

/-- The ordinary projection columns retain the large entrance parameter powers. -/
theorem solution :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y →
      let b := y 1 + y 3
      let Q := fderiv ℝ (fderiv ℝ entranceStablePhase) y
      |entranceStablePhase y - y 0| ≤ C * b ^ 2 / k ∧
      |entranceStablePartial y 0 - 1| ≤ C * b ^ 2 / k ^ 2 ∧
      |entranceStablePartial y 1| ≤ C * b / k ∧
      |entranceStablePartial y 3| ≤ C * b / k ∧
      |Q (Pi.single 0 1) (Pi.single 0 1)| ≤ C * b ^ 2 / k ^ 3 ∧
      |Q (Pi.single 1 1) (Pi.single 0 1)| ≤ C * b / k ^ 2 ∧
      |Q (Pi.single 3 1) (Pi.single 0 1)| ≤ C * b / k ^ 2 := by
  obtain ⟨C, hC, HC⟩ := exists_stableBoundaryProjection_refined_derivatives
  refine ⟨8 * (C + 8), by positivity, ?_⟩
  intro k y hk hy
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  have hk0 : 0 < k := by linarith
  have hL : k / 2 ≤ y 0 + 1 := by linarith [(entranceRegion_phase hk hy).1]
  have hb : 0 ≤ y 1 + y 3 := add_nonneg hy.2.2.1.1 hy.2.2.2.2.1
  have hscale (a q : ℝ) (ha : 0 ≤ a) (hq : 0 ≤ q) (n : ℕ) :
      a / (y 0 + 1) ^ n * q ≤ 2 ^ n * a * q / k ^ n := by
    calc
      _ ≤ a / (k / 2) ^ n * q := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left ha (pow_pos (by positivity) _) (pow_le_pow_left₀ (by positivity) hL n)) hq
      _ = _ := by simp only [div_pow]; field_simp
  have h0 : stableRestriction (Pi.single (0 : Fin 4) (1 : ℝ)) = Pi.single 0 1 := by
    ext i; fin_cases i <;> simp [stableRestriction]
  have h1 : stableRestriction (Pi.single (1 : Fin 4) (1 : ℝ)) = Pi.single 1 1 := by
    ext i; fin_cases i <;> simp [stableRestriction]
  have h3 : stableRestriction (Pi.single (3 : Fin 4) (1 : ℝ)) = Pi.single 2 1 := by
    ext i; fin_cases i <;> simp [stableRestriction]
  obtain ⟨hpM, hpz, hpMM, hpMz, _⟩ := HC (stableRestriction y) hm hu hw
  have H0 := hpM (Pi.single 0 1) (by simp) (by simp)
  have H1 := hpz (Pi.single 1 1) (by simp)
  have H3 := hpz (Pi.single 2 1) (by simp)
  have H00 := hpMM (Pi.single 0 1) (Pi.single 0 1) (by simp) (by simp) (by simp) (by simp)
  have H01 := hpMz (Pi.single 0 1) (Pi.single 1 1) (by simp) (by simp) (by simp)
  have H03 := hpMz (Pi.single 0 1) (Pi.single 2 1) (by simp) (by simp) (by simp)
  have hsym := (contDiffAt_entranceStablePhase_two hm hu hw).isSymmSndFDerivAt (by norm_num)
  dsimp only
  rw [hsym.eq (Pi.single 1 1) (Pi.single 0 1), hsym.eq (Pi.single 3 1) (Pi.single 0 1)]
  simp only [entranceStablePartial, entranceStablePhase_fderiv hm hu hw,
    entranceStablePhase_hessian hm hu hw, h0, h1, h3]
  have Hval : |entranceStablePhase y - y 0| ≤ 8 / (y 0 + 1) * (y 1 + y 3) ^ 2 := by
    have H := (stableBoundaryProjection_exists (m := y 0) hm (by simp) hu.le hw.le).2.2.2.2
    rw [abs_of_nonneg hy.2.2.1.1, abs_of_nonneg hy.2.2.2.2.1] at H
    convert! H using 1
    ring
  simp only [stableRestriction_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Pi.single_eq_same, Pi.norm_single, norm_one, mul_one,
    abs_of_nonneg hy.2.2.1.1, abs_of_nonneg hy.2.2.2.2.1] at H0 H1 H3 H00 H01 H03 ⊢
  have HB (a q : ℝ) (ha : 0 ≤ a) (hq : 0 ≤ q) (n : ℕ) (hconst : 2 ^ n * a ≤ 8 * (C + 8)) :
      a / (y 0 + 1) ^ n * q ≤ 8 * (C + 8) * q / k ^ n :=
    (hscale a q ha hq n).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hconst hq) (pow_pos hk0 n).le)
  refine ⟨?_, H0.trans (HB C _ hC.le (sq_nonneg _) 2 (by nlinarith)),
    ?_, ?_, H00.trans (HB C _ hC.le (sq_nonneg _) 3 (by nlinarith)),
    H01.trans (HB C _ hC.le hb 2 (by nlinarith)),
    H03.trans (HB C _ hC.le hb 2 (by nlinarith))⟩
  · simpa using Hval.trans (by simpa using HB 8 _ (by norm_num) (sq_nonneg (y 1 + y 3)) 1 (by nlinarith))
  · simpa using H1.trans (by simpa using HB C _ hC.le hb 1 (by nlinarith))
  · simpa using H3.trans (by simpa using HB C _ hC.le hb 1 (by nlinarith))
