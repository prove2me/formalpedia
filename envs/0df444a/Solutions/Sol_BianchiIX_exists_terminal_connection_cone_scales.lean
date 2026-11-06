-- Prove2me | solution 1 for BianchiIX.exists_terminal_connection_cone_scales
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T23:44:25.684773+00:00
-- url     : https://prove2.me/submissions/b09b009b-4f83-4645-89ef-3832a1e58d0e

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_TerminalConeData
import Definitions.Def_BianchiIX_EntrancePhaseResponseData
import Theorems.Thm_BianchiIX_exists_terminalConnectionLogWalls_cone_uniform
import Theorems.Thm_BianchiIX_exists_terminalConnection_sqrt_bounds_uniform
import Theorems.Thm_BianchiIX_exists_terminal_phase_cone_bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section
open BianchiIX
open Filter
open scoped Topology

section
noncomputable section
open BianchiIX

private theorem BianchiIX.sqrt_log_small_bound {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    Real.sqrt x * (1 + |Real.log x|) ≤ 2 := by
  have hs := Real.sqrt_pos.mpr hx
  have H := Real.one_sub_inv_le_log_of_pos hs
  rw [Real.log_sqrt hx.le] at H
  have H' := mul_le_mul_of_nonneg_left H hs.le
  rw [mul_sub, mul_one, mul_inv_cancel₀ hs.ne'] at H'
  rw [abs_of_nonpos (Real.log_nonpos hx.le hx1)]
  nlinarith only [H', hs.le]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.terminal_strong_log_bound {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) :
    v ^ (19 / 24 : ℝ) * (1 + |Real.log v|) ≤ 24 * v ^ (3 / 4 : ℝ) := by
  have hp := Real.rpow_pos_of_pos hv (1 / 24 : ℝ)
  have H := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hp) hp.le
  rw [mul_sub, mul_one, mul_inv_cancel₀ hp.ne', Real.log_rpow hv] at H
  have Hsmall : v ^ (1 / 24 : ℝ) * (1 + |Real.log v|) ≤ 24 := by
    rw [abs_of_nonpos (Real.log_nonpos hv.le hv1)]
    nlinarith only [H, hp.le]
  have Hsplit : v ^ (19 / 24 : ℝ) = v ^ (3 / 4 : ℝ) * v ^ (1 / 24 : ℝ) := by
    rw [← Real.rpow_add hv]
    norm_num
  rw [Hsplit, mul_assoc]
  exact (mul_le_mul_of_nonneg_left Hsmall (Real.rpow_nonneg hv.le _)).trans_eq (by ring)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.terminal_scaled_wall_power {α v w A p : ℝ} (hα : 0 < α) (hv : 0 ≤ v)
    (hw : 0 ≤ w) (hA : 1 ≤ A) (hp : 0 ≤ p ∧ p ≤ 1) (hscale : v ≤ A * w / α ^ 2) :
    v ^ p ≤ A * α ^ (-(2 * p)) * w ^ p := by
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have hAp : A ^ p ≤ A := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hA hp.2
  calc
    _ ≤ (A * w / α ^ 2) ^ p := Real.rpow_le_rpow hv hscale hp.1
    _ = A ^ p * w ^ p / α ^ (2 * p) := by
      rw [Real.div_rpow (mul_nonneg hA0 hw) (sq_nonneg α), Real.mul_rpow hA0 hw,
        ← Real.rpow_natCast α 2, ← Real.rpow_mul hα.le]
      norm_num
    _ ≤ A * w ^ p / α ^ (2 * p) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hAp (Real.rpow_nonneg hw _)) (Real.rpow_nonneg hα.le _)
    _ = _ := by rw [Real.rpow_neg hα.le]; ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.terminal_strong_cone_power {α v w A β : ℝ} (hα : 0 < α)
    (hv : 0 < v ∧ v ≤ 1) (hw : 0 < w) (hA : 1 ≤ A) (hscale : v ≤ A * w / α ^ 2) :
    α ^ β * (v ^ (19 / 24 : ℝ) * (1 + |Real.log v|) + α * v ^ (19 / 24 : ℝ) / Real.sqrt w) ≤
      24 * A * (α ^ (β - 3 / 2) * w ^ (3 / 4 : ℝ) + α ^ (β - 7 / 12) * w ^ (7 / 24 : ℝ)) := by
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have H3 := terminal_scaled_wall_power hα hv.1.le hw.le hA (by norm_num : 0 ≤ (3 / 4 : ℝ) ∧ (3 / 4 : ℝ) ≤ 1) hscale
  have H19 := terminal_scaled_wall_power hα hv.1.le hw.le hA (by norm_num : 0 ≤ (19 / 24 : ℝ) ∧ (19 / 24 : ℝ) ≤ 1) hscale
  norm_num at H3 H19
  have Hid1 : α ^ β * (24 * (A * α ^ (-(3 / 2 : ℝ)) * w ^ (3 / 4 : ℝ))) =
      24 * A * α ^ (β - 3 / 2) * w ^ (3 / 4 : ℝ) := by
    rw [show β - 3 / 2 = β + -(3 / 2 : ℝ) by ring, Real.rpow_add hα]
    ring
  have Hid2 : α ^ β * (α * (A * α ^ (-(19 / 12 : ℝ)) * w ^ (19 / 24 : ℝ)) / Real.sqrt w) =
      A * α ^ (β - 7 / 12) * w ^ (7 / 24 : ℝ) := by
    have hαpow : α ^ (β - 7 / 12) = α ^ β * α * α ^ (-(19 / 12 : ℝ)) := by
      rw [show β - 7 / 12 = (β + 1) + -(19 / 12 : ℝ) by ring,
        Real.rpow_add hα, Real.rpow_add hα, Real.rpow_one]
    have hwpow : w ^ (19 / 24 : ℝ) / Real.sqrt w = w ^ (7 / 24 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hw]
      norm_num
    rw [hαpow, show α ^ β * (α * (A * α ^ (-(19 / 12 : ℝ)) * w ^ (19 / 24 : ℝ)) / Real.sqrt w) =
      A * (α ^ β * α * α ^ (-(19 / 12 : ℝ))) * (w ^ (19 / 24 : ℝ) / Real.sqrt w) by ring, hwpow]
  have H1 := mul_le_mul_of_nonneg_left ((terminal_strong_log_bound hv.1 hv.2).trans
    (mul_le_mul_of_nonneg_left H3 (by norm_num : (0 : ℝ) ≤ 24))) (Real.rpow_nonneg hα.le β)
  rw [Hid1] at H1
  have H2 := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left H19 hα.le) (Real.sqrt_nonneg w)) (Real.rpow_nonneg hα.le β)
  rw [Hid2] at H2
  have Hpos : 0 ≤ A * α ^ (β - 7 / 12) * w ^ (7 / 24 : ℝ) := by positivity
  nlinarith only [H1, H2, Hpos]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.terminal_weak_cone_power {α v w U W A : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hv : 0 < v ∧ v ≤ 1) (hU : 0 < U) (hW : 0 < W) (hA : 1 ≤ A)
    (hwscale : Real.sqrt w ≤ A / α * Real.sqrt U)
    (hvscale : Real.sqrt v ≤ A / α * Real.sqrt W) :
    α ^ 2 * Real.sqrt w * Real.sqrt v *
      (|Real.log v| + 1 / α + 1 / Real.sqrt W + 1 / Real.sqrt U) ≤
        4 * A ^ 2 * (Real.sqrt U + Real.sqrt W) := by
  have hα0 : 0 < α := hα.1
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have hAA : A ≤ A ^ 2 := by nlinarith only [hA]
  have hlog : Real.sqrt v * |Real.log v| ≤ 2 := by
    have H := sqrt_log_small_bound hv.1 hv.2
    nlinarith only [H, Real.sqrt_nonneg v]
  have hscaled : α ^ 2 * Real.sqrt w ≤ A * Real.sqrt U := calc
    _ ≤ α ^ 2 * (A / α * Real.sqrt U) := mul_le_mul_of_nonneg_left hwscale (sq_nonneg α)
    _ = α * (A * Real.sqrt U) := by field_simp
    _ ≤ _ := mul_le_of_le_one_left (by positivity) hα.2
  have hprod : α ^ 2 * Real.sqrt w * Real.sqrt v ≤ A ^ 2 * Real.sqrt U * Real.sqrt W := calc
    _ ≤ α ^ 2 * (A / α * Real.sqrt U) * (A / α * Real.sqrt W) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hwscale (sq_nonneg α)) hvscale (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by field_simp
  have Hlog : α ^ 2 * Real.sqrt w * Real.sqrt v * |Real.log v| ≤ 2 * A * Real.sqrt U := calc
    _ = (α ^ 2 * Real.sqrt w) * (Real.sqrt v * |Real.log v|) := by ring
    _ ≤ (A * Real.sqrt U) * 2 := mul_le_mul hscaled hlog (by positivity) (by positivity)
    _ = _ := by ring
  have Ha : α ^ 2 * Real.sqrt w * Real.sqrt v * (1 / α) ≤ A * Real.sqrt U := calc
    _ ≤ α ^ 2 * (A / α * Real.sqrt U) * 1 * (1 / α) := by
      gcongr
      exact Real.sqrt_le_one.mpr hv.2
    _ = _ := by field_simp
  have HU : α ^ 2 * Real.sqrt w * Real.sqrt v * (1 / Real.sqrt U) ≤ A ^ 2 * Real.sqrt W :=
    (mul_le_mul_of_nonneg_right hprod (by positivity)).trans_eq (by field_simp [(Real.sqrt_pos.mpr hU).ne'])
  have HW : α ^ 2 * Real.sqrt w * Real.sqrt v * (1 / Real.sqrt W) ≤ A ^ 2 * Real.sqrt U :=
    (mul_le_mul_of_nonneg_right hprod (by positivity)).trans_eq (by field_simp [(Real.sqrt_pos.mpr hW).ne'])
  nlinarith only [Hlog, Ha, HU, HW, mul_le_mul_of_nonneg_right hAA (Real.sqrt_nonneg U),
    mul_nonneg (sq_nonneg A) (Real.sqrt_nonneg W)]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.sqrt_wall_ratio_of_scaled_log {x a p α C : ℝ} (hx : 0 < x) (hα : 0 < α)
    (hC : 0 ≤ C) (hp : 3 / (4 * α ^ 2) ≤ |p|)
    (H : α ^ 2 * Real.sqrt x * |a / x| ≤ C) :
    |a| / (Real.sqrt x * |p|) ≤ 2 * C := by
  have hp0 : 0 < |p| := (by positivity : 0 < 3 / (4 * α ^ 2)).trans_le hp
  have hden : 1 / 2 ≤ α ^ 2 * |p| := by
    have H' := (div_le_iff₀ (by positivity : 0 < 4 * α ^ 2)).mp hp
    nlinarith only [H']
  have hcancel : Real.sqrt x * |a / x| = |a| / Real.sqrt x := by
    rw [abs_div, abs_of_pos hx]
    calc
      _ = (Real.sqrt x / x) * |a| := by ring
      _ = (1 / Real.sqrt x) * |a| := by rw [Real.sqrt_div_self']
      _ = _ := by ring
  have Hid : |a| / (Real.sqrt x * |p|) =
      (α ^ 2 * Real.sqrt x * |a / x|) / (α ^ 2 * |p|) := by
    rw [mul_assoc (α ^ 2), hcancel]
    field_simp [hα.ne', hp0.ne', (Real.sqrt_pos.mpr hx).ne']
  rw [Hid]
  exact ((div_le_div_of_nonneg_right H (by positivity)).trans
    (div_le_div_of_nonneg_left hC (by norm_num : (0 : ℝ) < 1 / 2) hden)).trans_eq (by ring)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.hasFDerivAt_entranceLogWalls {y : ProjectiveState} (k : ℝ)
    (hu : y 1 ≠ 0) (hw : y 3 ≠ 0) :
    HasFDerivAt (entranceLogWalls k)
      (ContinuousLinearMap.pi (![(y 1)⁻¹ • ContinuousLinearMap.proj 1,
        k ^ 2 • ((y 3)⁻¹ • ContinuousLinearMap.proj 3)] : Fin 2 → (ProjectiveState →L[ℝ] ℝ))) y := by
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 4) y).log hu
  · exact ((hasFDerivAt_apply (𝕜 := ℝ) (3 : Fin 4) y).log hw).const_mul (k ^ 2)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.entranceLogWalls_fderiv_apply {y : ProjectiveState} (k : ℝ)
    (hu : y 1 ≠ 0) (hw : y 3 ≠ 0) (v : ProjectiveState) :
    fderiv ℝ (entranceLogWalls k) y v = entranceWallTangent k y v := by
  rw [(hasFDerivAt_entranceLogWalls k hu hw).fderiv]
  ext i
  fin_cases i <;> simp [entranceWallTangent, div_eq_mul_inv, mul_comm]

end
end

section
noncomputable section
open BianchiIX
open Filter Set
open scoped Topology

private theorem BianchiIX.terminalConnectionLogWalls_fderiv {h : ℝ} {Y : ExitTailState}
    (hstate : DifferentiableAt ℝ (terminalConnectionState h) Y)
    (hu : terminalConnectionState h Y 1 ≠ 0) (hw : terminalConnectionState h Y 3 ≠ 0)
    (d : ExitTailState) :
    fderiv ℝ (terminalConnectionLogWalls h) Y d =
      ![fderiv ℝ (terminalConnectionState h) Y d 1 / terminalConnectionState h Y 1,
        fderiv ℝ (terminalConnectionState h) Y d 3 / terminalConnectionState h Y 3] := by
  have HD := (hasFDerivAt_entranceLogWalls 1 hu hw).differentiableAt.hasFDerivAt.comp Y hstate.hasFDerivAt
  change fderiv ℝ (entranceLogWalls 1 ∘ terminalConnectionState h) Y d = _
  rw [HD.fderiv, ContinuousLinearMap.comp_apply, entranceLogWalls_fderiv_apply 1 hu hw]
  simp only [entranceWallTangent, one_pow, one_mul]

end
end


/-- Formula (D.37) for the actual terminal passage, including both phase powers. -/
theorem solution :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η₀ : ℝ, (0 < η₀ ∧ η₀ ≤ δ) →
      ∀ J : ℕ, 4 ≤ J → ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b U W : ℝ,
      η₀ ≤ η → η ≤ δ → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |U| + |W| ≤ b → 0 < U → 0 < W →
      let Y : ExitTailState := ![2 + 2 * α, U, W]
      let h := η * α ^ J
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalConnectionState h) Y ∧
        ContDiffAt ℝ 2 (terminalConnectionPhase h) Y ∧
        0 < terminalConnectionState h Y 1 ∧ 0 < terminalConnectionState h Y 3 ∧
        ∀ d : ExitTailState, d 0 = 1 → |d 1| ≤ Real.sqrt U → |d 2| ≤ Real.sqrt W →
          let p := fderiv ℝ (terminalConnectionPhase h) Y d
          p < 0 ∧ 3 / (4 * α ^ 2) ≤ |p| ∧
          |fderiv ℝ (terminalConnectionState h) Y d 1| / (Real.sqrt (terminalConnectionState h Y 1) * |p|) ≤
            C * (α ^ (((J : ℝ) - 5) / 2) * W ^ (3 / 4 : ℝ) + α ^ ((J : ℝ) / 2 - 19 / 12) * W ^ (7 / 24 : ℝ)) ∧
          |fderiv ℝ (terminalConnectionState h) Y d 3| / (Real.sqrt (terminalConnectionState h Y 3) * |p|) ≤
            C * (Real.sqrt U + Real.sqrt W) := by
  obtain ⟨δp, hδp, hδphi, HP⟩ := exists_terminal_phase_cone_bounds
  obtain ⟨δl, hδl, _, HL⟩ := exists_terminalConnectionLogWalls_cone_uniform
  let δ := min δp δl
  have hδhi : δ ≤ 1 / 40000 := (min_le_left _ _).trans hδphi
  refine ⟨δ, lt_min hδp hδl, hδhi, ?_⟩
  intro η₀ hη₀ J hJ
  obtain ⟨_, _, εp, hεp, HP'⟩ := HP η₀ ⟨hη₀.1, hη₀.2.trans (min_le_left _ _)⟩ J hJ
  obtain ⟨B, hB, εl, hεl, HL'⟩ := HL η₀ ⟨hη₀.1, hη₀.2.trans (min_le_right _ _)⟩ J (by omega)
  obtain ⟨A, hA, εa, hεa, HA⟩ := exists_terminalConnection_sqrt_bounds_uniform
    ⟨hη₀.1, hη₀.2.trans hδhi⟩ (by omega : 2 ≤ J)
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  have hAA : A ≤ A ^ 2 := by nlinarith only [hA]
  let C := 48 * A ^ 2 * B
  have hC : 1 ≤ C := by
    dsimp only [C]
    nlinarith only [hA, hAA, mul_le_mul_of_nonneg_left hB (sq_nonneg A)]
  refine ⟨C, hC, min εp (min εl εa), lt_min hεp (lt_min hεl hεa), ?_⟩
  intro η α b U W hηlo hηhi hα hb hsmall hsum hU hW Y h
  have hα0 : 0 < α := hα.1
  have hsp := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hα.1.le _))
  have hsl := hsmall.trans (mul_le_mul_of_nonneg_right
    ((min_le_right _ _).trans (min_le_left _ _)) (pow_nonneg hα.1.le _))
  have hsa := hsmall.trans (mul_le_mul_of_nonneg_right
    ((min_le_right _ _).trans (min_le_right _ _)) (pow_nonneg hα.1.le _))
  obtain ⟨_, Hphase, _, Hphasecone⟩ := HP' η α b U W hηlo (hηhi.trans (min_le_left _ _)) hα hb hsp hsum hU hW
  obtain ⟨HV, Hstate, HoutU, HoutW, _, Hlogs⟩ := HL' η α b U W hηlo (hηhi.trans (min_le_right _ _))
    hα hb hsl hsum hU hW
  obtain ⟨Hv, Hsu, Hsv, Hsw, Hvscale, HUdec, HWdec⟩ := HA η α b U W hηlo (hηhi.trans hδhi) hα hb hsa hsum hU hW
  let z := terminalEntranceInput h Y
  have hzv : 0 < z 2 := Hv.1
  let β := ((J : ℝ) - 2) / 2
  let P := α ^ (((J : ℝ) - 5) / 2) * W ^ (3 / 4 : ℝ) + α ^ ((J : ℝ) / 2 - 19 / 12) * W ^ (7 / 24 : ℝ)
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have Hpow := terminal_strong_cone_power (β := β) hα.1 ⟨Hv.1, Hv.2.le⟩ hW hA Hvscale
  rw [show β - 3 / 2 = ((J : ℝ) - 5) / 2 by dsimp only [β]; ring,
    show β - 7 / 12 = (J : ℝ) / 2 - 19 / 12 by dsimp only [β]; ring] at Hpow
  have Hweak := terminal_weak_cone_power hα ⟨Hv.1, Hv.2.le⟩ hU hW hA Hsw Hsv
  have Hroot : Real.sqrt (terminalConnectionState h Y 1) ≤ α ^ β * (z 2) ^ (19 / 24 : ℝ) :=
    HUdec.trans (mul_le_mul_of_nonneg_right Hsu (Real.rpow_nonneg Hv.1.le _))
  have hlog : -Real.log (z 2) = |Real.log (z 2)| := (abs_of_nonpos (Real.log_nonpos Hv.1.le Hv.2.le)).symm
  refine ⟨HV, Hstate, Hphase, HoutU, HoutW, ?_⟩
  intro d hd0 hd1 hd2 p
  obtain ⟨_, Hpneg, Hp⟩ := Hphasecone d hd0 hd1 hd2
  obtain ⟨HLu, HLw⟩ := Hlogs d hd0 hd1 hd2
  let l := fderiv ℝ (terminalConnectionLogWalls h) Y d
  change |l 0| ≤ B * ((1 + -Real.log (z 2)) / α ^ 2 + 1 / (α * Real.sqrt W)) at HLu
  change |l 1| ≤ B * (-Real.log (z 2) + 1 / α + 1 / Real.sqrt W + 1 / Real.sqrt U) at HLw
  rw [hlog] at HLu HLw
  have HUscaled : α ^ 2 * Real.sqrt (terminalConnectionState h Y 1) * |l 0| ≤ 24 * A * B * P := calc
    _ ≤ α ^ 2 * (α ^ β * (z 2) ^ (19 / 24 : ℝ)) *
        (B * ((1 + |Real.log (z 2)|) / α ^ 2 + 1 / (α * Real.sqrt W))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left Hroot (sq_nonneg α)) HLu (abs_nonneg _) (by positivity)
    _ = B * (α ^ β * ((z 2) ^ (19 / 24 : ℝ) * (1 + |Real.log (z 2)|) +
        α * (z 2) ^ (19 / 24 : ℝ) / Real.sqrt W)) := by field_simp [hα.1.ne']
    _ ≤ B * (24 * A * P) := mul_le_mul_of_nonneg_left Hpow hB0
    _ = _ := by ring
  have HWscaled : α ^ 2 * Real.sqrt (terminalConnectionState h Y 3) * |l 1| ≤
      4 * A ^ 2 * B * (Real.sqrt U + Real.sqrt W) := calc
    _ ≤ α ^ 2 * (Real.sqrt (z 3) * Real.sqrt (z 2)) *
        (B * (|Real.log (z 2)| + 1 / α + 1 / Real.sqrt W + 1 / Real.sqrt U)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left HWdec (sq_nonneg α)) HLw (abs_nonneg _) (by positivity)
    _ = B * (α ^ 2 * Real.sqrt (z 3) * Real.sqrt (z 2) *
        (|Real.log (z 2)| + 1 / α + 1 / Real.sqrt W + 1 / Real.sqrt U)) := by ring
    _ ≤ B * (4 * A ^ 2 * (Real.sqrt U + Real.sqrt W)) := mul_le_mul_of_nonneg_left Hweak hB0
    _ = _ := by ring
  have HD := terminalConnectionLogWalls_fderiv (Hstate.differentiableAt (by norm_num)) HoutU.ne' HoutW.ne' d
  have Hdu : l 0 = fderiv ℝ (terminalConnectionState h) Y d 1 / terminalConnectionState h Y 1 := congrFun HD 0
  have Hdw : l 1 = fderiv ℝ (terminalConnectionState h) Y d 3 / terminalConnectionState h Y 3 := congrFun HD 1
  rw [Hdu] at HUscaled
  rw [Hdw] at HWscaled
  have HUratio := sqrt_wall_ratio_of_scaled_log HoutU hα.1 (by positivity : 0 ≤ 24 * A * B * P) Hp HUscaled
  have HWratio := sqrt_wall_ratio_of_scaled_log HoutW hα.1
    (by positivity : 0 ≤ 4 * A ^ 2 * B * (Real.sqrt U + Real.sqrt W)) Hp HWscaled
  refine ⟨Hpneg, Hp, HUratio.trans ?_, HWratio.trans ?_⟩
  · dsimp only [C]
    nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAA hB0) hP]
  · dsimp only [C]
    nlinarith only [mul_nonneg (mul_nonneg (sq_nonneg A) hB0) (add_nonneg (Real.sqrt_nonneg U) (Real.sqrt_nonneg W))]
