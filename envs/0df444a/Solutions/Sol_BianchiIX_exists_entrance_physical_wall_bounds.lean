-- Prove2me | solution 1 for BianchiIX.exists_entrance_physical_wall_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T17:32:30.48604+00:00
-- url     : https://prove2.me/submissions/84749619-a4b6-415b-ab34-6c602cc81673

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
import Theorems.Thm_BianchiIX_entrance_terminal_wall_forms
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

private theorem BianchiIX.entrance_terminal_correction_bound {A T b k X Y Z E : ℝ}
    (hA : 0 ≤ A) (hT : 0 ≤ T) (hZ : 0 ≤ Z)
    (hb : b ^ 2 / k ^ 2 ≤ 4) (hX : X ≤ A * Z) (hY : Y ≤ (2 + 4 * A) * Z)
    (hE : E ≤ T * (b ^ 2 / k ^ 2 * X + Y)) :
    E ≤ T * (2 + 8 * A) * Z := by
  have HX := (mul_le_mul_of_nonneg_left hX (by positivity : 0 ≤ b ^ 2 / k ^ 2)).trans
    (mul_le_mul_of_nonneg_right hb (mul_nonneg hA hZ))
  apply hE.trans
  calc
    _ ≤ T * (4 * (A * Z) + (2 + 4 * A) * Z) := mul_le_mul_of_nonneg_left (add_le_add HX hY) hT
    _ = _ := by ring

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


/-- All three physical wall-input columns follow directly from terminal amplitude products. -/
theorem solution :
    ∃ C > (0 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧
      ∀ (y : ProjectiveState) (θ : ℝ),
      let k := coreRadius (y 0) (y 2)
      7 / 4 ≤ k → 1 ≤ y 0 → (0 < y 1 ∧ y 1 ≤ ε) → (0 < y 2 ∧ y 2 < 1) →
      (0 < y 3 ∧ y 3 ≤ ε) → (θ = 1 ∨ (θ = 1 / k ^ 2 ∧ k * (y 1 + y 3) ^ 2 ≤ 1)) →
      ∃ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ ∧
      let z := entranceRadialCoordinates y
      let ω := Real.exp (-2 * (-Real.log (y 2)) / k)
      let F := fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2)
      |fderiv ℝ F z (Pi.single 1 1)| ≤ C * y 2 / k ∧
      |fderiv ℝ F z (Pi.single 2 1)| ≤ C * (y 1 + y 2 * (y 3) ^ 2) ∧
      |fderiv ℝ F z (Pi.single 3 1)| ≤ C * (y 1 * y 2 + (y 2) ^ 2 * y 3 * (θ + ω)) / k := by
  obtain ⟨A, hA, ε, hε, hεsmall, HA⟩ := exists_entrance_return_full_columns
  obtain ⟨T, hT, HT⟩ := exists_entrance_return_correction_variation
  let B := T * (2 + 8 * A)
  let C := A + B
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨C, add_pos hA hB, ε, hε, hεsmall, ?_⟩
  intro y θ k hk hm hu hv hw hθ
  obtain ⟨Ψ, HΨ, HQ, HU, HW⟩ := HA y θ hk hm hu hv hw hθ
  refine ⟨Ψ, HΨ, ?_⟩
  intro z ω F
  let p := entranceReturnState y
  let b := p 1 + p 3
  let Q := fun z => entranceStableRadius (entranceReturnState (Ψ z))
  let Logs := fun z => entranceLogWalls 1 (entranceReturnState (Ψ z))
  let E := fun z => entranceRadiusCorrection (entranceReturnState (Ψ z))
  let J := y 1 * y 2 + (y 2) ^ 2 * y 3 * (θ + ω)
  let K := y 1 + y 2 * (y 3) ^ 2
  have hk0 : 0 < k := by linarith
  have hk1 : 1 ≤ k := by linarith
  have hu' : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000 := ⟨hu.1.le, hu.2.trans hεsmall⟩
  have hw' : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000 := ⟨hw.1.le, hw.2.trans hεsmall⟩
  have hθ01 : 0 ≤ θ ∧ θ ≤ 1 := by
    rcases hθ with rfl | ⟨rfl, _⟩
    · norm_num
    · exact ⟨by positivity, (div_le_one (sq_pos_of_pos hk0)).mpr (one_le_pow₀ hk1)⟩
  have hL : 0 ≤ -Real.log (y 2) := neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le)
  have hω : 0 ≤ ω ∧ ω ≤ 1 := ⟨(Real.exp_pos _).le,
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by nlinarith only [hL]) hk0.le)⟩
  have hJ : 0 ≤ J := by dsimp [J]; positivity [hu.1, hv.1, hw.1, hθ01.1, hω.1]
  have hK : 0 ≤ K := by dsimp [K]; positivity [hu.1, hv.1]
  have HR := (entranceReturn_regular hk hm hu' hv hw').1
  have hp : entranceRegion k p := entranceReturn_region hk hm hu' hv hw' _ ⟨HR.1.1.1.le, le_rfl⟩
  have hb : 0 ≤ b := add_nonneg hp.2.2.1.1 hp.2.2.2.2.1
  have Hw := entranceReturn_terminal_weights hk hm hu' hv hw'
  have Hforms := entrance_terminal_wall_forms hA.le hk1 ⟨hu.1, by linarith [hu'.2]⟩
    ⟨hv.1, hv.2.le⟩ ⟨hw.1, by linarith [hw'.2]⟩ hp.2.2.1.1 hp.2.2.2.2.1 hθ01.1 hω
    Hw.1 Hw.2.2.2.1 Hw.2.2.2.2.1 Hw.2.2.2.2.2
  have hQu : |fderiv ℝ Q z (Pi.single 1 1)| ≤ A * (y 2 / k) := by simpa only [mul_div_assoc] using HQ.2.1
  have hQw : |fderiv ℝ Q z (Pi.single 3 1)| ≤ A * (J / k) := by
    have Hnum : y 1 * y 2 + θ * (y 2) ^ 2 * y 3 ≤ J := by
      have H : 0 ≤ (y 2) ^ 2 * y 3 * ω := by positivity [hw.1, hω.1]
      dsimp [J]
      nlinarith only [H]
    apply HQ.2.2.2.trans
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right Hnum hk0.le) hA.le
  have hQv : |fderiv ℝ Q z (Pi.single 2 1)| ≤ A * K := by
    apply HQ.2.2.1.trans (mul_le_mul_of_nonneg_left ?_ hA.le)
    have H := mul_le_mul_of_nonneg_right hθ01.2 (show 0 ≤ y 2 * (y 3) ^ 2 by positivity [hv.1])
    dsimp [K]
    nlinarith only [H]
  have hdiag {x a c : ℝ} (ha : 0 ≤ a) (h : |x - a| ≤ c) : |x| ≤ a + c := by
    have H := abs_add_le (x - a) a
    rw [sub_add_cancel, abs_of_nonneg ha] at H
    linarith only [H, h]
  have hUu := hdiag (show 0 ≤ 1 / y 1 by positivity [hu.1]) HU.2.1
  have hWw := hdiag (show 0 ≤ 1 / y 3 by positivity [hw.1]) HW.2.2.2
  have hwall (i : Fin 4) {SU SW Z : ℝ}
      (hU : |fderiv ℝ Logs z (Pi.single i 1) 0| ≤ SU)
      (hW : |fderiv ℝ Logs z (Pi.single i 1) 1| ≤ SW)
      (hform : b / k * (p 1 * SU + p 3 * SW) ≤ (2 + 4 * A) * Z) :
      b / k * (p 1 * |fderiv ℝ Logs z (Pi.single i 1) 0| + p 3 * |fderiv ℝ Logs z (Pi.single i 1) 1|) ≤
        (2 + 4 * A) * Z :=
    (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hU hp.2.2.1.1)
      (mul_le_mul_of_nonneg_left hW hp.2.2.2.2.1)) (div_nonneg hb hk0.le)).trans hform
  have hcorr (i : Fin 4) := HT y hk hm ⟨hu.1, hu'.2⟩ hv ⟨hw.1, hw'.2⟩ Ψ HΨ (Pi.single i 1)
  have hEu : |fderiv ℝ E z (Pi.single 1 1)| ≤ B * (y 2 / k) :=
    entrance_terminal_correction_bound hA.le hT.le (div_nonneg hv.1.le hk0.le) Hforms.1 hQu
      (hwall 1 hUu HW.2.1 Hforms.2.1) (hcorr 1)
  have hEw : |fderiv ℝ E z (Pi.single 3 1)| ≤ B * (J / k) :=
    entrance_terminal_correction_bound hA.le hT.le (div_nonneg hJ hk0.le) Hforms.1 hQw
      (hwall 3 HU.2.2.2 hWw Hforms.2.2.1) (hcorr 3)
  have hEv : |fderiv ℝ E z (Pi.single 2 1)| ≤ B * K :=
    entrance_terminal_correction_bound hA.le hT.le hK Hforms.1 hQv
      (hwall 2 HU.2.2.1 HW.2.2.1 Hforms.2.2.2) (hcorr 2)
  have hphysical (i : Fin 4) {Z : ℝ}
      (hQ : |fderiv ℝ Q z (Pi.single i 1)| ≤ A * Z)
      (hE : |fderiv ℝ E z (Pi.single i 1)| ≤ B * Z) : |fderiv ℝ F z (Pi.single i 1)| ≤ C * Z := by
    have HE := HΨ.return_correction_difference hk hm hu' hv hw' (Pi.single i 1)
    have hid : fderiv ℝ F z (Pi.single i 1) = fderiv ℝ Q z (Pi.single i 1) - fderiv ℝ E z (Pi.single i 1) := by
      linarith only [HE]
    rw [hid]
    exact (abs_sub _ _).trans ((add_le_add hQ hE).trans_eq (by dsimp [C]; ring))
  refine ⟨?_, hphysical 2 hQv hEv, ?_⟩
  · simpa only [mul_div_assoc] using hphysical 1 hQu hEu
  · simpa only [mul_div_assoc] using hphysical 3 hQw hEw
