-- Prove2me | solution 1 for BianchiIX.exists_entranceRadialDrift_refined_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T17:10:43.906442+00:00
-- url     : https://prove2.me/submissions/b3273641-fd88-4270-93bc-0a059d6edd20

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
import Definitions.Def_BianchiIX_Dynamics_EntranceRegion
import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Definitions.Def_BianchiIX_EntrancePhaseResponseData
import Theorems.Thm_BianchiIX_contDiffAt_stableBoundaryProjection_two_in_band
import Theorems.Thm_BianchiIX_entrance_phase_bounds
import Theorems.Thm_BianchiIX_exists_entranceRadialDrift_basic_bounds
import Theorems.Thm_BianchiIX_exists_entranceRadialStrong_derivative_bound
import Theorems.Thm_BianchiIX_exists_entranceRadialStrong_radial_bounds
import Theorems.Thm_BianchiIX_exists_entranceRadialWeakCoefficient_refined_bounds
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

private theorem BianchiIX.coreRadius_pos {m v : ℝ} (hv : 0 < v) : 0 < coreRadius m v := by
  apply Real.sqrt_pos.mpr
  unfold coreEnergy
  positivity

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connection_coupling_bounds {u v w : ℝ} (hu : 0 ≤ u)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    -u ^ 2 ≤ coupling u v w ∧ coupling u v w ≤ 2 * u := by
  unfold coupling
  constructor
  · nlinarith only [mul_nonneg hu hv.1, mul_nonneg hu hw.1]
  · nlinarith only [mul_le_mul_of_nonneg_left hv.2 hu,
      mul_le_mul_of_nonneg_left hw.2 hu, sq_nonneg u]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entrance_speed_bounds {k m u v w : ℝ} (hk : 7 / 4 ≤ k)
    (hm : 4 / 5 * k ≤ m - 1 ∧ m - 1 ≤ 101 / 100 * k)
    (hu : 0 ≤ u ∧ u ≤ 1 / 10000) (hv : 0 ≤ v ∧ v ≤ 1)
    (hw : 0 ≤ w ∧ w ≤ 1 / 10000) :
    3 / 4 * k ≤ connectionSpeed m u v w ∧ connectionSpeed m u v w ≤ 21 / 20 * k := by
  have hC := connection_coupling_bounds hu.1 hv ⟨hw.1, by linarith [hw.2]⟩
  have hu2 : u ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hu.1 hu.2 2
  unfold connectionSpeed
  constructor <;> nlinarith only [hm.1, hm.2, hC.1, hC.2, hu.2, hu2, hk]

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
open Set

private theorem BianchiIX.entranceRegion_speed {k : ℝ} {y : ProjectiveState} (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) :
    3 / 4 * k ≤ entranceClockRate y ∧ entranceClockRate y ≤ 21 / 20 * k :=
  entrance_speed_bounds hk (entranceRegion_phase hk hy) hy.2.2.1 hy.2.2.2.1 hy.2.2.2.2

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.entranceRegion_clock_pos {k : ℝ} {y : ProjectiveState} (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) :
    0 < entranceClockRate y := by linarith [(entranceRegion_speed hk hy).1]

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

private theorem BianchiIX.entranceStableRadius_pos {y : ProjectiveState} (hv : 0 < y 2) :
    0 < entranceStableRadius y := coreRadius_pos hv

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_entranceStableRadius_two {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (hv : 0 < y 2) :
    ContDiffAt ℝ 2 entranceStableRadius y := by
  have hP := contDiffAt_entranceStablePhase_two hm hu hw
  have hV : ContDiffAt ℝ 2 (fun z : ProjectiveState => z 2) y := by fun_prop
  exact (((hP.sub contDiffAt_const).pow 2).add (hV.pow 2)).sqrt (by positivity)

end
end

section
noncomputable section
open BianchiIX

local instance  : NormedAddCommGroup (ProjectiveState →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance  : NormedSpace ℝ (ProjectiveState →L[ℝ] ℝ) := inferInstance
private theorem BianchiIX.contDiffAt_entranceStablePartial_one {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (i : Fin 4) :
    ContDiffAt ℝ 1 (fun z => entranceStablePartial z i) y :=
  ((contDiffAt_entranceStablePhase_two hm hu hw).fderiv_right
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply contDiffAt_const

end
end

section
noncomputable section
open BianchiIX

local instance  : NormedAddCommGroup (ProjectiveState →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance  : NormedSpace ℝ (ProjectiveState →L[ℝ] ℝ) := inferInstance
private theorem BianchiIX.contDiffAt_entranceWeakNumerator_one {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) :
    ContDiffAt ℝ 1 entranceWeakNumerator y := by
  have hP := (contDiffAt_entranceStablePhase_two hm hu hw).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hPM := contDiffAt_entranceStablePartial_one hm hu hw 0
  unfold entranceWeakNumerator
  fun_prop

end
end

section
noncomputable section
open BianchiIX

local instance  : NormedAddCommGroup (ProjectiveState →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance  : NormedSpace ℝ (ProjectiveState →L[ℝ] ℝ) := inferInstance
private theorem BianchiIX.contDiffAt_entranceRadialCoefficients_one {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200)
    (hv : 0 < y 2) (hD : entranceClockRate y ≠ 0) :
    ContDiffAt ℝ 1 entranceRadialStrongCoefficient y ∧
      ContDiffAt ℝ 1 entranceRadialWeakCoefficient y := by
  have hP := (contDiffAt_entranceStablePhase_two hm hu hw).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hpartial := contDiffAt_entranceStablePartial_one hm hu hw
  have hr := (contDiffAt_entranceStableRadius_two hm hu hw hv).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hclock : ContDiffAt ℝ 1 entranceClockRate y := by
    unfold entranceClockRate connectionSpeed coupling
    fun_prop
  have hden := mul_ne_zero (entranceStableRadius_pos hv).ne' hD
  constructor
  · unfold entranceRadialStrongCoefficient
    apply ContDiffAt.div _ (hr.mul hclock) hden
    fun_prop
  · exact (contDiffAt_entranceWeakNumerator_one hm hu hw).div (hr.mul hclock) hden

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.EntranceRadialInverseAt.wall_coordinates {y : ProjectiveState} {Ψ : ProjectiveState → ProjectiveState}
    (H : EntranceRadialInverseAt y Ψ) :
    ∀ᶠ z in 𝓝 (entranceRadialCoordinates y), Ψ z 1 = z 1 ∧ Ψ z 2 = z 2 ∧ Ψ z 3 = z 3 := by
  filter_upwards [H.right_inverse] with z hz
  exact ⟨by simpa [entranceRadialCoordinates] using congrArg (fun v : ProjectiveState => v 1) hz,
    by simpa [entranceRadialCoordinates] using congrArg (fun v : ProjectiveState => v 2) hz,
    by simpa [entranceRadialCoordinates] using congrArg (fun v : ProjectiveState => v 3) hz⟩

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.EntranceRadialInverseAt.coefficients_regular {y : ProjectiveState} {k : ℝ}
    {Ψ : ProjectiveState → ProjectiveState} (H : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) :
    ContDiffAt ℝ 1 (fun z => entranceRadialStrongCoefficient (Ψ z)) (entranceRadialCoordinates y) ∧
      ContDiffAt ℝ 1 (fun z => entranceRadialWeakCoefficient (Ψ z)) (entranceRadialCoordinates y) := by
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  have hreg := contDiffAt_entranceRadialCoefficients_one hm hu hw hv (entranceRegion_clock_pos hk hy).ne'
  have hA : ContDiffAt ℝ 1 entranceRadialStrongCoefficient (Ψ (entranceRadialCoordinates y)) := by
    rw [H.apply_base]; exact hreg.1
  have hB : ContDiffAt ℝ 1 entranceRadialWeakCoefficient (Ψ (entranceRadialCoordinates y)) := by
    rw [H.apply_base]; exact hreg.2
  have hΨ := H.contDiffAt.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  exact ⟨hA.comp _ hΨ, hB.comp _ hΨ⟩

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.EntranceRadialInverseAt.drift_radial_derivative {y : ProjectiveState} {k : ℝ}
    {Ψ : ProjectiveState → ProjectiveState} (H : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) :
    let z := entranceRadialCoordinates y
    fderiv ℝ (fun z => entranceRadialDrift (Ψ z)) z (Pi.single 0 1) =
      y 1 * y 2 * fderiv ℝ (fun z => entranceRadialStrongCoefficient (Ψ z)) z (Pi.single 0 1) +
      y 2 ^ 2 * fderiv ℝ (fun z => entranceRadialWeakCoefficient (Ψ z)) z (Pi.single 0 1) := by
  have heq : (fun z => entranceRadialDrift (Ψ z)) =ᶠ[𝓝 (entranceRadialCoordinates y)]
      (fun z => z 1 * z 2 * entranceRadialStrongCoefficient (Ψ z) + z 2 ^ 2 * entranceRadialWeakCoefficient (Ψ z)) := by
    filter_upwards [H.wall_coordinates] with z hz
    simp only [entranceRadialDrift, hz.1, hz.2.1]
  obtain ⟨hA, hB⟩ := H.coefficients_regular hk hy hv
  have hd (i : Fin 4) := hasFDerivAt_apply (𝕜 := ℝ) i (entranceRadialCoordinates y)
  have hsum := (((hd 1).mul (hd 2)).mul (hA.differentiableAt (by norm_num)).hasFDerivAt).add
    (((hd 2).pow 2).mul (hB.differentiableAt (by norm_num)).hasFDerivAt)
  change HasFDerivAt (fun z => z 1 * z 2 * entranceRadialStrongCoefficient (Ψ z) + z 2 ^ 2 * entranceRadialWeakCoefficient (Ψ z)) _
    (entranceRadialCoordinates y) at hsum
  dsimp only
  rw [heq.fderiv_eq, hsum.fderiv]
  simp [add_apply, smul_apply, ContinuousLinearMap.proj_apply, entranceRadialCoordinates, Pi.mul_apply]

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.EntranceRadialInverseAt.drift_differential {y : ProjectiveState} {k : ℝ}
    {Ψ : ProjectiveState → ProjectiveState} (H : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) :
    let z := entranceRadialCoordinates y
    DifferentiableAt ℝ (fun z => entranceRadialDrift (Ψ z)) z ∧
      ∀ v : ProjectiveState,
        fderiv ℝ (fun z => entranceRadialDrift (Ψ z)) z v =
          (v 1 * y 2 + y 1 * v 2) * entranceRadialStrongCoefficient y +
          y 1 * y 2 * fderiv ℝ (fun z => entranceRadialStrongCoefficient (Ψ z)) z v +
          2 * y 2 * v 2 * entranceRadialWeakCoefficient y +
          y 2 ^ 2 * fderiv ℝ (fun z => entranceRadialWeakCoefficient (Ψ z)) z v := by
  have heq : (fun z => entranceRadialDrift (Ψ z)) =ᶠ[𝓝 (entranceRadialCoordinates y)]
      (fun z => z 1 * z 2 * entranceRadialStrongCoefficient (Ψ z) + z 2 ^ 2 * entranceRadialWeakCoefficient (Ψ z)) := by
    filter_upwards [H.wall_coordinates] with z hz
    simp only [entranceRadialDrift, hz.1, hz.2.1]
  obtain ⟨hA, hB⟩ := H.coefficients_regular hk hy hv
  have hd (i : Fin 4) := hasFDerivAt_apply (𝕜 := ℝ) i (entranceRadialCoordinates y)
  have hsum := (((hd 1).mul (hd 2)).mul (hA.differentiableAt (by norm_num)).hasFDerivAt).add
    (((hd 2).pow 2).mul (hB.differentiableAt (by norm_num)).hasFDerivAt)
  change HasFDerivAt (fun z => z 1 * z 2 * entranceRadialStrongCoefficient (Ψ z) + z 2 ^ 2 * entranceRadialWeakCoefficient (Ψ z)) _
    (entranceRadialCoordinates y) at hsum
  have hactual := hsum.congr_of_eventuallyEq heq
  refine ⟨hactual.differentiableAt, fun v => ?_⟩
  rw [hactual.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, Pi.mul_apply]
  rw [H.apply_base]
  simp only [entranceRadialCoordinates, Matrix.cons_val_one, Matrix.cons_val]
  ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.EntranceRadialInverseAt.drift_wall_partials {y : ProjectiveState} {k : ℝ}
    {Ψ : ProjectiveState → ProjectiveState} (H : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) :
    let z := entranceRadialCoordinates y
    let LA := fderiv ℝ (fun z => entranceRadialStrongCoefficient (Ψ z)) z
    let LB := fderiv ℝ (fun z => entranceRadialWeakCoefficient (Ψ z)) z
    let LG := fderiv ℝ (fun z => entranceRadialDrift (Ψ z)) z
    LG (Pi.single 1 1) = y 2 * entranceRadialStrongCoefficient y + y 1 * y 2 * LA (Pi.single 1 1) +
        y 2 ^ 2 * LB (Pi.single 1 1) ∧
      LG (Pi.single 3 1) = y 1 * y 2 * LA (Pi.single 3 1) + y 2 ^ 2 * LB (Pi.single 3 1) := by
  constructor <;> simp [(H.drift_differential hk hy hv).2]

end
end


set_option maxHeartbeats 600000 in
/-- Equation (C.24), retaining the additional two inverse powers in the pure weak-wall terms. -/
theorem solution :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y →
      k * (y 1 + y 3) ^ 2 ≤ 1 → 0 < y 2 →
      ∀ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ →
        let LG := fderiv ℝ (fun z => entranceRadialDrift (Ψ z)) (entranceRadialCoordinates y)
        |entranceRadialDrift y| ≤ C * (y 1 * y 2 + y 2 ^ 2 * y 3 ^ 2 / k ^ 4) ∧
        |LG (Pi.single 0 1)| ≤ C * (y 1 * y 2 / k ^ 2 + y 2 ^ 2 * y 3 ^ 2 / k ^ 5) ∧
        |y 1 * LG (Pi.single 1 1)| ≤ C * (y 1 * y 2) ∧
        |y 3 * LG (Pi.single 3 1)| ≤ C * (y 1 * y 2 * y 3 + y 2 ^ 2 * y 3 ^ 2 / k ^ 4) := by
  obtain ⟨A, hA, HA⟩ := exists_entranceRadialStrong_derivative_bound
  obtain ⟨R, hR, HR⟩ := exists_entranceRadialStrong_radial_bounds
  obtain ⟨B, hB, HB⟩ := exists_entranceRadialWeakCoefficient_refined_bounds
  obtain ⟨T, hT, HT⟩ := exists_entranceRadialDrift_basic_bounds
  refine ⟨A + B + R + T, by positivity, ?_⟩
  intro k y hk hy hsmall hv Ψ H
  let b := y 1 + y 3
  let z := entranceRadialCoordinates y
  have hu0 := hy.2.2.1.1
  have hv0 := hy.2.2.2.1.1
  have hw0 := hy.2.2.2.2.1
  have hb : 0 ≤ b := add_nonneg hu0 hw0
  have hb1 : b ≤ 1 := by dsimp [b]; linarith [hy.2.2.1.2, hy.2.2.2.2.2]
  have hk1 : 1 ≤ k := by linarith
  have hk0 : 0 < k := by linarith
  have hk2 : 1 ≤ k ^ 2 := one_le_pow₀ hk1
  have huv : 0 ≤ y 1 * y 2 := mul_nonneg hu0 hv0
  have hV2 : y 2 ^ 2 ≤ y 2 := by nlinarith only [hv0, hy.2.2.2.1.2]
  have hnum : y 2 ^ 2 * y 1 * b ≤ y 1 * y 2 := by
    have Hp := ((mul_le_mul_of_nonneg_left hb1 (sq_nonneg (y 2))).trans (by simpa using hV2))
    nlinarith only [mul_le_mul_of_nonneg_left Hp hu0]
  have hscale0 : y 2 ^ 2 * y 1 * b / k ^ 2 ≤ y 1 * y 2 :=
    (div_le_self (by positivity) hk2).trans hnum
  have hscaleR : y 2 ^ 2 * y 1 * b / k ^ 3 ≤ y 1 * y 2 / k ^ 2 :=
    (div_le_div_of_nonneg_right hnum (by positivity)).trans
      (div_le_div_of_nonneg_left huv (by positivity) (pow_le_pow_right₀ hk1 (by norm_num : 2 ≤ 3)))
  have hscaleW : y 2 ^ 2 * y 1 * y 3 / k ^ 2 ≤ y 1 * y 2 * y 3 := by
    calc
      _ ≤ y 2 ^ 2 * y 1 * y 3 := div_le_self (by positivity) hk2
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hV2 (mul_nonneg hu0 hw0)]
  have hstrong := HA k y hk hy hv Ψ H
  have hAval : |entranceRadialStrongCoefficient y| ≤ A := by
    linarith only [hstrong, norm_nonneg (fderiv ℝ (fun z => entranceRadialStrongCoefficient (Ψ z)) z)]
  have hAnorm : ‖fderiv ℝ (fun z => entranceRadialStrongCoefficient (Ψ z)) z‖ ≤ A := by
    linarith only [hstrong, abs_nonneg (entranceRadialStrongCoefficient y)]
  have hAw : |fderiv ℝ (fun z => entranceRadialStrongCoefficient (Ψ z)) z (Pi.single 3 1)| ≤ A := by
    have Hp := ((fderiv ℝ (fun z => entranceRadialStrongCoefficient (Ψ z)) z).le_opNorm (Pi.single 3 1)).trans
      (mul_le_mul_of_nonneg_right hAnorm (norm_nonneg _))
    simpa [Pi.norm_single] using Hp
  have hAr := (HR k y hk hy hv Ψ H).2.1
  obtain ⟨hB0, hBr, _, hBw⟩ := HB k y hk hy hsmall hv Ψ H
  have habs (c a : ℝ) (hc : 0 ≤ c) : |c * a| = c * |a| := by rw [abs_mul, abs_of_nonneg hc]
  have hmerge (a c x t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) : a * x + c * (x + t) ≤ (a + c) * (x + t) := by
    nlinarith only [mul_nonneg ha ht]
  have hG : |entranceRadialDrift y| ≤ (A + B) * (y 1 * y 2 + y 2 ^ 2 * y 3 ^ 2 / k ^ 4) := by
    calc
      _ ≤ y 1 * y 2 * |entranceRadialStrongCoefficient y| + y 2 ^ 2 * |entranceRadialWeakCoefficient y| := by
        unfold entranceRadialDrift
        exact (abs_add_le _ _).trans (add_le_add (le_of_eq (habs _ _ huv)) (le_of_eq (habs _ _ (sq_nonneg _))))
      _ ≤ y 1 * y 2 * A + y 2 ^ 2 * (B * (y 1 * b / k ^ 2 + y 3 ^ 2 / k ^ 4)) :=
        add_le_add (mul_le_mul_of_nonneg_left hAval huv) (mul_le_mul_of_nonneg_left hB0 (sq_nonneg _))
      _ = A * (y 1 * y 2) + B * (y 2 ^ 2 * y 1 * b / k ^ 2 + y 2 ^ 2 * y 3 ^ 2 / k ^ 4) := by ring
      _ ≤ A * (y 1 * y 2) + B * (y 1 * y 2 + y 2 ^ 2 * y 3 ^ 2 / k ^ 4) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add hscale0 le_rfl) hB.le)
      _ ≤ _ := hmerge _ _ _ _ hA.le (by positivity)
  have hGr : |fderiv ℝ (fun z => entranceRadialDrift (Ψ z)) z (Pi.single 0 1)| ≤
      (R + B) * (y 1 * y 2 / k ^ 2 + y 2 ^ 2 * y 3 ^ 2 / k ^ 5) := by
    rw [H.drift_radial_derivative hk hy hv]
    calc
      _ ≤ y 1 * y 2 * |fderiv ℝ (fun z => entranceRadialStrongCoefficient (Ψ z)) z (Pi.single 0 1)| +
          y 2 ^ 2 * |fderiv ℝ (fun z => entranceRadialWeakCoefficient (Ψ z)) z (Pi.single 0 1)| :=
        (abs_add_le _ _).trans (add_le_add (le_of_eq (habs _ _ huv)) (le_of_eq (habs _ _ (sq_nonneg _))))
      _ ≤ y 1 * y 2 * (R / k ^ 2) + y 2 ^ 2 * (B * (y 1 * b / k ^ 3 + y 3 ^ 2 / k ^ 5)) :=
        add_le_add (mul_le_mul_of_nonneg_left hAr huv) (mul_le_mul_of_nonneg_left hBr (sq_nonneg _))
      _ = R * (y 1 * y 2 / k ^ 2) + B * (y 2 ^ 2 * y 1 * b / k ^ 3 + y 2 ^ 2 * y 3 ^ 2 / k ^ 5) := by ring
      _ ≤ R * (y 1 * y 2 / k ^ 2) + B * (y 1 * y 2 / k ^ 2 + y 2 ^ 2 * y 3 ^ 2 / k ^ 5) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add hscaleR le_rfl) hB.le)
      _ ≤ _ := hmerge _ _ _ _ hR.le (by positivity)
  have hGw : |y 3 * fderiv ℝ (fun z => entranceRadialDrift (Ψ z)) z (Pi.single 3 1)| ≤
      (A + B) * (y 1 * y 2 * y 3 + y 2 ^ 2 * y 3 ^ 2 / k ^ 4) := by
    rw [(H.drift_wall_partials hk hy hv).2, habs _ _ hw0]
    calc
      _ ≤ y 3 * (y 1 * y 2 * |fderiv ℝ (fun z => entranceRadialStrongCoefficient (Ψ z)) z (Pi.single 3 1)| +
          y 2 ^ 2 * |fderiv ℝ (fun z => entranceRadialWeakCoefficient (Ψ z)) z (Pi.single 3 1)|) := by
        apply mul_le_mul_of_nonneg_left _ hw0
        exact (abs_add_le _ _).trans (add_le_add (le_of_eq (habs _ _ huv)) (le_of_eq (habs _ _ (sq_nonneg _))))
      _ ≤ y 3 * (y 1 * y 2 * A + y 2 ^ 2 * (B * (y 1 / k ^ 2 + y 3 / k ^ 4))) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hAw huv)
          (mul_le_mul_of_nonneg_left hBw (sq_nonneg _))) hw0
      _ = A * (y 1 * y 2 * y 3) + B * (y 2 ^ 2 * y 1 * y 3 / k ^ 2 + y 2 ^ 2 * y 3 ^ 2 / k ^ 4) := by ring
      _ ≤ A * (y 1 * y 2 * y 3) + B * (y 1 * y 2 * y 3 + y 2 ^ 2 * y 3 ^ 2 / k ^ 4) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add hscaleW le_rfl) hB.le)
      _ ≤ _ := hmerge _ _ _ _ hA.le (by positivity)
  have hGu := (HT k y hk hy hv Ψ H).2.2.1
  dsimp only
  refine ⟨hG.trans ?_, hGr.trans ?_, hGu.trans ?_, hGw.trans ?_⟩
  all_goals
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith only [hA, hB, hR, hT]
