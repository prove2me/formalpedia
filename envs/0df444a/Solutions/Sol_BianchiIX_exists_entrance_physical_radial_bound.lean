-- Prove2me | solution 1 for BianchiIX.exists_entrance_physical_radial_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T17:32:27.706977+00:00
-- url     : https://prove2.me/submissions/5923aaac-9440-46ca-b571-fe2ba429875e

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_EntranceRegion
import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Definitions.Def_BianchiIX_Dynamics_EntranceReturn
import Definitions.Def_BianchiIX_EntrancePhaseResponseData
import Theorems.Thm_BianchiIX_contDiffAt_stableBoundaryProjection_two_in_band
import Theorems.Thm_BianchiIX_entranceReturn_active_component
import Theorems.Thm_BianchiIX_entranceReturn_decay
import Theorems.Thm_BianchiIX_entranceReturn_region
import Theorems.Thm_BianchiIX_entranceReturn_regular
import Theorems.Thm_BianchiIX_entrance_phase_bounds
import Theorems.Thm_BianchiIX_entrance_radial_terminal_correction
import Theorems.Thm_BianchiIX_entrance_terminal_wall_weights
import Theorems.Thm_BianchiIX_exists_entrance_return_correction_variation
import Theorems.Thm_BianchiIX_exists_entrance_return_full_columns
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
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX

private theorem BianchiIX.mul_neg_log_le_one {w : ℝ} (hw : 0 < w) : w * (-Real.log w) ≤ 1 := by
  have H := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hw) hw.le
  have hid : w * (1 - w⁻¹) = w - 1 := by field_simp
  rw [hid] at H
  nlinarith only [H, hw]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.affine_mul_exp_neg_le_one (x : ℝ) : (1 + x) * Real.exp (-x) ≤ 1 := by
  have H := mul_le_mul_of_nonneg_right (Real.add_one_le_exp x) (Real.exp_pos (-x)).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at H
  simpa only [add_comm] using H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entrance_terminal_clock_weights {k L : ℝ} (hk : 1 ≤ k) (hL : 0 ≤ L) :
    (0 ≤ Real.exp (-k * L / 3) ∧ Real.exp (-k * L / 3) ≤ 1) ∧
    (0 ≤ Real.exp (-L / k) ∧ Real.exp (-L / k) ≤ 1) ∧
    L * Real.exp (-k * L / 3) ≤ 3 / k ∧
    Real.exp (-L / k) ^ 2 = Real.exp (-2 * L / k) ∧
    (1 + L / k) * Real.exp (-2 * L / k) ≤ 1 := by
  have hk0 : 0 < k := by linarith
  refine ⟨⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by nlinarith only [mul_nonneg hk0.le hL])⟩,
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hL) hk0.le)⟩, ?_, ?_, ?_⟩
  · have H := affine_mul_exp_neg_le_one (k * L / 3)
    rw [show -(k * L / 3) = -k * L / 3 by ring] at H
    apply (le_div_iff₀ hk0).mpr
    nlinarith only [H, Real.exp_pos (-k * L / 3)]
  · rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  · have H := affine_mul_exp_neg_le_one (2 * L / k)
    rw [show -(2 * L / k) = -2 * L / k by ring] at H
    have hcoeff : 1 + L / k ≤ 1 + 2 * L / k := by
      rw [mul_div_assoc]
      linarith only [div_nonneg hL hk0.le]
    exact (mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos _).le).trans H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entrance_phase_waiting_budget {u v w θ : ℝ}
    (hu : 0 ≤ u) (hv : 0 < v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) (hθ : 0 ≤ θ ∧ θ ≤ 1) :
    0 ≤ u * v + θ * (v * w) ^ 2 ∧
      u * v + θ * (v * w) ^ 2 ≤ u + w ∧
      (-Real.log v) * (u * v + θ * (v * w) ^ 2) ≤ u + w := by
  have hv0 := hv.1.le
  have hw0 := hw.1
  have hθ0 := hθ.1
  have hW2 : w ^ 2 ≤ w := by nlinarith only [mul_le_mul_of_nonneg_left hw.2 hw.1]
  have htail : θ * v * w ^ 2 ≤ w :=
    ((mul_le_of_le_one_left (sq_nonneg w)
      ((mul_le_of_le_one_left hv0 hθ.2).trans hv.2)).trans hW2)
  have hP : 0 ≤ u + θ * v * w ^ 2 := by positivity
  have hPbound : u + θ * v * w ^ 2 ≤ u + w := add_le_add le_rfl htail
  have hLv : (-Real.log v) * v ≤ 1 := by simpa only [mul_comm] using mul_neg_log_le_one hv.1
  refine ⟨by positivity, ?_, ?_⟩
  · calc
      _ = v * (u + θ * v * w ^ 2) := by ring
      _ ≤ u + θ * v * w ^ 2 := mul_le_of_le_one_left hP hv.2
      _ ≤ _ := hPbound
  · calc
      _ = ((-Real.log v) * v) * (u + θ * v * w ^ 2) := by ring
      _ ≤ u + θ * v * w ^ 2 := mul_le_of_le_one_left hP hLv
      _ ≤ _ := hPbound

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

private theorem BianchiIX.entranceReturn_terminal_weights {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) :
    let k := coreRadius (y 0) (y 2)
    let L := -Real.log (y 2)
    let ω := Real.exp (-2 * L / k)
    let p := entranceReturnState y
    let b := p 1 + p 3
    b ^ 2 ≤ 2 * (y 1 * y 2 + (y 2) ^ 2 * (y 3) ^ 2 * ω) ∧
    k * L * b * p 1 ≤ 6 * y 1 * y 2 ∧
    (L / k) * b * p 3 ≤ 3 * y 1 * y 2 + (L / k) * ((y 2) ^ 2 * (y 3) ^ 2 * ω) ∧
    b * p 1 ≤ 2 * y 1 * y 2 ∧
    b * p 3 ≤ y 3 * (y 1 * y 2 + (y 2) ^ 2 * y 3 * ω) ∧
    b ≤ 2 * y 2 := by
  intro k L ω p b
  have hk1 : 1 ≤ k := by linarith
  have hL : 0 ≤ L := neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le)
  have H := entrance_terminal_clock_weights hk1 hL
  have HR := (entranceReturn_regular hk hm hu hv hw).1
  have hreg : entranceRegion k p := entranceReturn_region hk hm hu hv hw _ ⟨HR.1.1.1.le, le_rfl⟩
  have hdec := entranceReturn_decay hk hm hu hv hw
  have HE := entrance_terminal_wall_weights hk1 hL ⟨hu.1, by linarith [hu.2]⟩
    ⟨hv.1.le, hv.2.le⟩ ⟨hw.1, by linarith [hw.2]⟩ hreg.2.2.1.1 hreg.2.2.2.2.1
    H.1 H.2.1 H.2.2.1 hdec.1 hdec.2
  simpa only [H.2.2.2.1] using HE

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

private theorem BianchiIX.hasFDerivAt_coreRadius_state {y : ProjectiveState} (hv : 0 < y 2) :
    HasFDerivAt (fun z : ProjectiveState => coreRadius (z 0) (z 2))
      ((1 / coreRadius (y 0) (y 2)) •
        ((y 0 - 1) • (ContinuousLinearMap.proj (0 : Fin 4) : ProjectiveState →L[ℝ] ℝ) +
          y 2 • (ContinuousLinearMap.proj (2 : Fin 4) : ProjectiveState →L[ℝ] ℝ))) y := by
  have H := ((((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) y).sub_const 1).pow 2).add
    ((hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 4) y).pow 2)).sqrt
      (by change (y 0 - 1) ^ 2 + y 2 ^ 2 ≠ 0; positivity)
  convert! H using 1
  ext v
  simp only [add_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  simp only [Pi.add_apply, Nat.reduceSub, pow_one, nsmul_eq_mul, Nat.cast_ofNat, coreRadius, coreEnergy]
  ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.EntranceRadialInverseAt.hasFDerivAt_return {y : ProjectiveState}
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) :
    HasFDerivAt (fun z => entranceReturnState (Ψ z))
      ((fderiv ℝ entranceReturnState y).comp (entranceRadialInverseDifferential y)) (entranceRadialCoordinates y) := by
  have hd : HasFDerivAt entranceReturnState (fderiv ℝ entranceReturnState y) (Ψ (entranceRadialCoordinates y)) := by
    rw [HΨ.apply_base]
    exact ((entranceReturn_regular hk hm hu hv hw).2.2.1.differentiableAt (by norm_num)).hasFDerivAt
  simpa only [Function.comp_def] using hd.comp (entranceRadialCoordinates y) HΨ.hasFDerivAt

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.EntranceRadialInverseAt.return_correction_difference {y : ProjectiveState}
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) (d : ProjectiveState) :
    let z := entranceRadialCoordinates y
    let Q := fun z => entranceStableRadius (entranceReturnState (Ψ z))
    let F := fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2)
    let E := fun z => entranceRadiusCorrection (entranceReturnState (Ψ z))
    fderiv ℝ E z d = fderiv ℝ Q z d - fderiv ℝ F z d := by
  intro z Q F E
  have HR := (entranceReturn_regular hk hm hu hv hw).1
  have hp : entranceRegion (coreRadius (y 0) (y 2)) (entranceReturnState y) :=
    entranceReturn_region hk hm hu hv hw _ ⟨HR.1.1.1.le, le_rfl⟩
  have hV : 0 < entranceReturnState y 2 := by
    rw [(entranceReturn_active_component hk hm hu hv hw).1]
    norm_num
  have hM : 2 ≤ entranceReturnState y 0 := by linarith [(entranceRegion_phase hk hp).1]
  have hU : |entranceReturnState y 1| < 1 / 200 := by rw [abs_of_nonneg hp.2.2.1.1]; linarith [hp.2.2.1.2]
  have hW : |entranceReturnState y 3| < 1 / 200 := by rw [abs_of_nonneg hp.2.2.2.2.1]; linarith [hp.2.2.2.2.2]
  have hg := (HΨ.hasFDerivAt_return hk hm hu hv hw).differentiableAt
  have hQ : DifferentiableAt ℝ Q z := by
    have hf : DifferentiableAt ℝ entranceStableRadius (entranceReturnState (Ψ z)) := by
      dsimp only [z]
      rw [HΨ.apply_base]
      exact (contDiffAt_entranceStableRadius_two hM hU hW hV).differentiableAt (by norm_num)
    have Hcomp := hf.comp z hg
    exact Hcomp
  have hF : DifferentiableAt ℝ F z := by
    have hf : DifferentiableAt ℝ (fun p : ProjectiveState => coreRadius (p 0) (p 2))
        (entranceReturnState (Ψ z)) := by
      dsimp only [z]
      rw [HΨ.apply_base]
      exact (hasFDerivAt_coreRadius_state hV).differentiableAt
    have Hcomp := hf.comp z hg
    exact Hcomp
  have H := hQ.hasFDerivAt.sub hF.hasFDerivAt
  change HasFDerivAt E (fderiv ℝ Q z - fderiv ℝ F z) z at H
  rw [H.fderiv, sub_apply]

end
end


/-- The radial column of the physical arrival retains the terminal weak decay in (C.39). -/
theorem solution :
    ∃ C > (0 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧
      ∀ (y : ProjectiveState) (θ : ℝ),
      let k := coreRadius (y 0) (y 2)
      7 / 4 ≤ k → 1 ≤ y 0 → (0 < y 1 ∧ y 1 ≤ ε) → (0 < y 2 ∧ y 2 < 1) →
      (0 < y 3 ∧ y 3 ≤ ε) → (θ = 1 ∨ (θ = 1 / k ^ 2 ∧ k * (y 1 + y 3) ^ 2 ≤ 1)) →
      ∃ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ ∧
      let z := entranceRadialCoordinates y
      let L := -Real.log (y 2)
      let ω := Real.exp (-2 * L / k)
      let F := fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2)
      let E := fun z => entranceRadiusCorrection (entranceReturnState (Ψ z))
      |fderiv ℝ E z (Pi.single 0 1)| ≤
        C * (y 1 * y 2 + (1 + L / k) * ((y 2) ^ 2 * (y 3) ^ 2 * ω)) / k ^ 2 ∧
      |fderiv ℝ F z (Pi.single 0 1) - 1| ≤
        C * (y 1 * y 2 + (y 2) ^ 2 * (y 3) ^ 2 * (θ + (1 + L / k) * ω)) / k ^ 2 := by
  obtain ⟨A, hA, ε, hε, hεsmall, HA⟩ := exists_entrance_return_full_columns
  obtain ⟨T, hT, HT⟩ := exists_entrance_return_correction_variation
  let B := T * (2 + 13 * A)
  let C := A + B
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 0 < C := add_pos hA hB
  have hBC : B ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ε, hε, hεsmall, ?_⟩
  intro y θ k hk hm hu hv hw hθ
  obtain ⟨Ψ, HΨ, HQ, HU, HW⟩ := HA y θ hk hm hu hv hw hθ
  refine ⟨Ψ, HΨ, ?_⟩
  intro z L ω F E
  let Q := fun z => entranceStableRadius (entranceReturnState (Ψ z))
  let Logs := fun z => entranceLogWalls 1 (entranceReturnState (Ψ z))
  let p := entranceReturnState y
  let P := y 1 * y 2
  let S := (y 2) ^ 2 * (y 3) ^ 2 * ω
  let H := P + θ * (y 2 * y 3) ^ 2
  let J := P + (1 + L / k) * S
  let R := P + (y 2) ^ 2 * (y 3) ^ 2 * (θ + (1 + L / k) * ω)
  have hk0 : 0 < k := by linarith
  have hk1 : 1 ≤ k := by linarith
  have hL : 0 ≤ L := neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le)
  have hθ01 : 0 ≤ θ ∧ θ ≤ 1 := by
    rcases hθ with rfl | ⟨rfl, _⟩
    · norm_num
    · exact ⟨by positivity, (div_le_one (sq_pos_of_pos hk0)).mpr (one_le_pow₀ hk1)⟩
  have hu' : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000 := ⟨hu.1.le, hu.2.trans hεsmall⟩
  have hw' : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000 := ⟨hw.1.le, hw.2.trans hεsmall⟩
  have hweights := entranceReturn_terminal_weights hk hm hu' hv hw'
  have hwait := entrance_phase_waiting_budget hu.1.le ⟨hv.1, hv.2.le⟩ ⟨hw.1.le, by linarith [hw'.2]⟩ hθ01
  have hH0 : 0 ≤ H := hwait.1
  have hH2 : H ≤ 2 := by linarith only [hwait.2.1, hu'.2, hw'.2]
  have hinc : |fderiv ℝ Q z (Pi.single 0 1) - 1| ≤ 2 * A := by
    apply HQ.1.trans
    calc
      A * H / k ^ 2 ≤ A * H := div_le_self (mul_nonneg hA.le hH0) (one_le_pow₀ hk1)
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hH2 hA.le]
  have hQ : |fderiv ℝ Q z (Pi.single 0 1)| ≤ 1 + 2 * A := by
    have Htriangle := abs_add_le (fderiv ℝ Q z (Pi.single 0 1) - 1) (1 : ℝ)
    simp only [sub_add_cancel, abs_one] at Htriangle
    linarith only [Htriangle, hinc]
  have HR := (entranceReturn_regular hk hm hu' hv hw').1
  have hp : entranceRegion k p := entranceReturn_region hk hm hu' hv hw' _ ⟨HR.1.1.1.le, le_rfl⟩
  have hS : 0 ≤ S := by dsimp [S, ω]; positivity
  have hJ : 0 ≤ J := by dsimp [J, P]; positivity [hu.1, hv.1]
  have hcorr := HT y hk hm ⟨hu.1, hu'.2⟩ hv ⟨hw.1, hw'.2⟩ Ψ HΨ (Pi.single 0 1)
  have hfast : k * L * (p 1 + p 3) * p 1 ≤ 6 * P := by
    simpa only [P, mul_assoc] using hweights.2.1
  have hslow : (L / k) * (p 1 + p 3) * p 3 ≤ 3 * P + (L / k) * S := by
    simpa only [P, S, mul_assoc] using hweights.2.2.1
  have HE : |fderiv ℝ E z (Pi.single 0 1)| ≤ B * J / k ^ 2 :=
    entrance_radial_terminal_correction hA.le hT.le hk0 hL hS hp.2.2.1.1 hp.2.2.2.2.1
      hweights.1 hfast hslow hQ HU.1 HW.1 hcorr
  have hHR : H ≤ R := by
    have hnonneg : 0 ≤ (1 + L / k) * S := by positivity
    dsimp [H, R, S] at *
    nlinarith only [hnonneg]
  have hJR : J ≤ R := by
    have hnonneg : 0 ≤ θ * (y 2 * y 3) ^ 2 := by positivity [hθ01.1]
    dsimp [J, R, S] at *
    nlinarith only [hnonneg]
  refine ⟨HE.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hBC hJ) (sq_nonneg k)), ?_⟩
  have hid : fderiv ℝ F z (Pi.single 0 1) - 1 =
      (fderiv ℝ Q z (Pi.single 0 1) - 1) - fderiv ℝ E z (Pi.single 0 1) := by
    have Hdiff := HΨ.return_correction_difference hk hm hu' hv hw' (Pi.single 0 1)
    linarith only [Hdiff]
  rw [hid]
  calc
    _ ≤ |fderiv ℝ Q z (Pi.single 0 1) - 1| + |fderiv ℝ E z (Pi.single 0 1)| := abs_sub _ _
    _ ≤ A * H / k ^ 2 + B * J / k ^ 2 := add_le_add HQ.1 HE
    _ = (A * H + B * J) / k ^ 2 := by ring
    _ ≤ (A * R + B * R) / k ^ 2 := div_le_div_of_nonneg_right
      (add_le_add (mul_le_mul_of_nonneg_left hHR hA.le) (mul_le_mul_of_nonneg_left hJR hB.le)) (sq_nonneg k)
    _ = _ := by dsimp [C, R, P]; ring
