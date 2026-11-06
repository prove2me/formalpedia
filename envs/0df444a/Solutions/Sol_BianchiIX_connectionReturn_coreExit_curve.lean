-- Prove2me | solution 1 for BianchiIX.connectionReturn_coreExit_curve
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T10:53:42.388527+00:00
-- url     : https://prove2.me/submissions/498c3a9a-856d-402a-8396-a68dfc58331d

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ConnectionEvents
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturn
import Definitions.Def_BianchiIX_Dynamics_ConnectionPhysicalReturn
import Definitions.Def_BianchiIX_Dynamics_CoreConnectionChart
import Theorems.Thm_BianchiIX_connectionReturn_regular
import Theorems.Thm_BianchiIX_connectionReturn_unit_cone
import Theorems.Thm_BianchiIX_homogeneous_cone_of_unit
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
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exp_neg_le_one_sub_half {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (-x) ≤ 1 - x / 2 := by
  have hp : 0 < x + 1 := by linarith only [hx]
  rw [Real.exp_neg]
  calc
    _ ≤ (x + 1)⁻¹ := inv_le_inv₀ (Real.exp_pos _) hp |>.mpr (Real.add_one_le_exp x)
    _ ≤ 1 - x / 2 := by
      rw [inv_eq_one_div]
      apply (div_le_iff₀ hp).mpr
      nlinarith only [mul_nonneg hx (sub_nonneg.mpr hx1)]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.homogeneous_phase_ratio_of_unit
    (D : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) {R a b A : ℝ}
    (hunit : ∀ z : Fin 3 → ℝ, R * z 0 = 1 → |z 1| ≤ a → |z 2| ≤ b →
      |D z 0 - 1| ≤ A)
    (v : Fin 3 → ℝ) (hc : R * v 0 ≠ 0)
    (hva : |v 1| ≤ a * |R * v 0|) (hvb : |v 2| ≤ b * |R * v 0|) :
    |D v 0 / (R * v 0) - 1| ≤ A := by
  let c := R * v 0
  have hc' : c ≠ 0 := hc
  let z := c⁻¹ • v
  have hz0 : R * z 0 = 1 := by
    change R * (c⁻¹ * v 0) = 1
    calc
      _ = c⁻¹ * c := by dsimp only [c]; ring
      _ = 1 := inv_mul_cancel₀ hc
  have hz (i : Fin 3) (s : ℝ) (hi : |v i| ≤ s * |c|) : |z i| ≤ s := by
    change |c⁻¹ * v i| ≤ s
    rw [abs_mul, abs_inv]
    calc
      _ ≤ |c|⁻¹ * (s * |c|) := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (abs_nonneg _))
      _ = s := by field_simp
  have H := hunit z hz0 (hz 1 a hva) (hz 2 b hvb)
  have hd : D z 0 = D v 0 / c := by
    dsimp only [z]
    rw [map_smul]
    change c⁻¹ * D v 0 = D v 0 / c
    ring
  rwa [hd] at H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_sq (a b : ℝ) : phaseNorm a b ^ 2 = a ^ 2 + b ^ 2 :=
  Real.sq_sqrt (by positivity)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_ge {a b : ℝ} (ha : 0 ≤ a) : a ≤ phaseNorm a b := by
  calc
    a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
    _ ≤ phaseNorm a b := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg b))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_pos {a b : ℝ} (ha : 0 < a) : 0 < phaseNorm a b :=
  ha.trans_le (phaseNorm_ge ha.le)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_ratio_bounds {a b : ℝ} (ha : 2 ≤ a) (hb : 0 ≤ b ∧ b ≤ 1) :
    7 / 8 ≤ a / phaseNorm a b ∧ a / phaseNorm a b ≤ 1 := by
  have ha0 : 0 < a := by linarith only [ha]
  have hn := phaseNorm_pos (b := b) ha0
  have hb2 : b ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hb.1 hb.2 2
  have ha2 : 4 ≤ a ^ 2 := by nlinarith only [ha, sq_nonneg (a - 2)]
  have hupper : phaseNorm a b ≤ 8 * a / 7 := by
    nlinarith only [phaseNorm_sq a b, hb2, ha2, hn, ha0]
  exact ⟨(le_div_iff₀ hn).mpr (by linarith only [hupper]),
    (div_le_one hn).mpr (phaseNorm_ge ha0.le)⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connection_cone_gap {μ L : ℝ} (hμ : 4 ≤ μ) (hL : 4 ≤ L) :
    1 / μ ≤ 1 - Real.exp (-L / (2 * μ)) ∧ 1 - Real.exp (-L / (2 * μ)) ≤ 1 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hx : 0 ≤ 2 / μ := by positivity
  have hx1 : 2 / μ ≤ 1 := (div_le_one hμ0).mpr (by linarith only [hμ])
  have H := exp_neg_le_one_sub_half hx hx1
  have Hexp : Real.exp (-L / (2 * μ)) ≤ Real.exp (-(2 / μ)) := by
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ -4 / (2 * μ) := div_le_div_of_nonneg_right (neg_le_neg hL) (by positivity)
      _ = _ := by ring
  refine ⟨?_, ?_⟩
  · have heq : 2 / μ / 2 = 1 / μ := by ring
    rw [heq] at H
    linarith only [H, Hexp]
  · linarith only [Real.exp_pos (-L / (2 * μ))]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasFDerivAt_connectionEntrancePhase (p : ConnectionParameters) :
    HasFDerivAt (fun q : ConnectionParameters => phaseNorm (q 0 + 1) 1)
      (((p 0 + 1) / phaseNorm (p 0 + 1) 1) •
        (ContinuousLinearMap.proj (0 : Fin 3) : ConnectionParameters →L[ℝ] ℝ)) p := by
  have ha := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) p).add_const 1
  have H := ((ha.pow 2).add_const 1).sqrt (by positivity : (p 0 + 1) ^ 2 + 1 ≠ 0)
  convert! H using 1
  · ext q
    simp [phaseNorm]
  · ext v
    simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.proj_apply]
    simp only [phaseNorm, one_pow]
    ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_connectionReturnPhysicalState {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    ContDiffAt ℝ 2 connectionReturnPhysicalState p := by
  have hstate := (connectionReturn_regular hμ hu hw).2.2.1
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · have hm := contDiffAt_pi.mp hstate 0
    exact ((((hm.neg.sub contDiffAt_const).pow 2).add contDiffAt_const).sqrt (by positivity))
  · exact contDiffAt_pi.mp hstate 1
  · exact contDiffAt_pi.mp hstate 2

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreExitConnectionParameters_phase {Z : CoreAngleState} (hK : 1 < Z 0) :
    phaseNorm (coreExitConnectionParameters Z 0 + 1) 1 = Z 0 := by
  have hs := Real.sq_sqrt (by nlinarith only [hK] : 0 ≤ Z 0 ^ 2 - 1)
  change Real.sqrt ((Real.sqrt (Z 0 ^ 2 - 1) - 1 + 1) ^ 2 + 1 ^ 2) = Z 0
  rw [show (Real.sqrt (Z 0 ^ 2 - 1) - 1 + 1) ^ 2 + 1 ^ 2 = Z 0 ^ 2 by nlinarith only [hs]]
  exact Real.sqrt_sq (by linarith only [hK])

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_coreExitConnectionParameters (n : WithTop ℕ∞) {Z : CoreAngleState} (hK : 1 < Z 0) :
    ContDiffAt ℝ n coreExitConnectionParameters Z := by
  have hs : Z 0 ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith only [hK] : 0 < Z 0 ^ 2 - 1)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreExitConnectionParameters] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreExitConnectionParameters_differential {Z : CoreAngleState} (hK : 1 < Z 0)
    (v : CoreAngleState) :
    let p := coreExitConnectionParameters Z
    let w := fderiv ℝ coreExitConnectionParameters Z v
    ((p 0 + 1) / phaseNorm (p 0 + 1) 1) * w 0 = v 0 ∧ w 1 = v 1 ∧ w 2 = v 2 := by
  intro p w
  have hc := (contDiffAt_coreExitConnectionParameters 1 hK).differentiableAt (by norm_num)
  have heq : (fun X => phaseNorm (coreExitConnectionParameters X 0 + 1) 1) =ᶠ[𝓝 Z]
      (fun X : CoreAngleState => X 0) := by
    filter_upwards [(continuous_apply 0).continuousAt.eventually (lt_mem_nhds hK)] with X hX
    exact coreExitConnectionParameters_phase hX
  have H := (hasFDerivAt_connectionEntrancePhase p).comp Z hc.hasFDerivAt
  have He := (H.congr_of_eventuallyEq heq.symm).unique (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) Z)
  have Hphase := congrArg (fun A : CoreAngleState →L[ℝ] ℝ => A v) He
  have hcomponent (i : Fin 2) : w i.succ = v i.succ := by
    have Hi : HasFDerivAt (fun X => coreExitConnectionParameters X i.succ)
        (ContinuousLinearMap.proj i.succ : CoreAngleState →L[ℝ] ℝ) Z := by
      fin_cases i <;> exact hasFDerivAt_apply _ _
    have Hd := Hi.fderiv
    rw [fderiv_apply hc i.succ] at Hd
    exact congrArg (fun A : CoreAngleState →L[ℝ] ℝ => A v) Hd
  exact ⟨Hphase, hcomponent 0, hcomponent 1⟩

end
end

/-- The connection preserves the actual curve cone and the sign of its radial slope. -/
theorem solution {f u w : ℝ → ℝ} {x ε : ℝ}
    (hf : DifferentiableAt ℝ f x) (hu : DifferentiableAt ℝ u x)
    (hw : DifferentiableAt ℝ w x) (hf1 : 1 < f x) (hdf : deriv f x < 0)
    (hε : 0 < ε ∧ ε ≤ 1 / 10000) (hsε : Real.sqrt ε ≤ 1 / 1000000)
    (hεL : ε ≤ Real.exp (-256))
    (hμ : 4 ≤ coreExitConnectionParameters ![f x, u x, w x] 0)
    (hu0 : 0 < u x ∧ u x ≤ ε / coreExitConnectionParameters ![f x, u x, w x] 0)
    (hw0 : 0 < w x ∧ w x ≤ ε)
    (hdu : |deriv u x| ≤ Real.sqrt (u x) * |deriv f x|)
    (hdw : |deriv w x| ≤ Real.sqrt (w x) * |deriv f x|) :
    let p := fun a => coreExitConnectionParameters ![f a, u a, w a]
    let G := fun a => connectionReturnPhysicalState (p a)
    DifferentiableAt ℝ G x ∧
      deriv (fun a => G a 0) x < 0 ∧
      |deriv (fun a => G a 0) x / deriv f x - 1| ≤ 1 / (4 * p x 0) ∧
      (3 / 4 ≤ deriv (fun a => G a 0) x / deriv f x ∧
        deriv (fun a => G a 0) x / deriv f x ≤ 5 / 4) ∧
      |deriv (fun a => G a 1) x| ≤ Real.sqrt (G x 1) * |deriv (fun a => G a 0) x| ∧
      |deriv (fun a => G a 2) x| ≤ Real.sqrt (G x 2) * |deriv (fun a => G a 0) x| := by
  intro p G
  let Z := fun a => ![f a, u a, w a]
  let v : CoreAngleState := ![deriv f x, deriv u x, deriv w x]
  have hZ : HasDerivAt Z v x := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hf.hasDerivAt
    · exact hu.hasDerivAt
    · exact hw.hasDerivAt
  have hc := (contDiffAt_coreExitConnectionParameters (Z := Z x) 1 hf1).differentiableAt (by norm_num)
  let ξ := fderiv ℝ coreExitConnectionParameters (Z x) v
  have hp : HasDerivAt p ξ x := hc.hasFDerivAt.comp_hasDerivAt x hZ
  have Hc := coreExitConnectionParameters_differential (Z := Z x) hf1 v
  change ((p x 0 + 1) / phaseNorm (p x 0 + 1) 1) * ξ 0 = deriv f x ∧
    ξ 1 = deriv u x ∧ ξ 2 = deriv w x at Hc
  have hμ0 : 0 < p x 0 := by linarith only [hμ]
  have hu' : 0 ≤ p x 1 ∧ p x 1 ≤ (1 / 10000) / p x 0 :=
    ⟨hu0.1.le, hu0.2.trans (div_le_div_of_nonneg_right hε.2 hμ0.le)⟩
  have hw' : 0 < p x 2 ∧ p x 2 ≤ 1 / 10000 := ⟨hw0.1, hw0.2.trans hε.2⟩
  have hG := (contDiffAt_connectionReturnPhysicalState hμ hu' hw').differentiableAt (by norm_num)
  let D := fderiv ℝ connectionReturnPhysicalState (p x)
  have HD : HasDerivAt G (D ξ) x := hG.hasFDerivAt.comp_hasDerivAt (f := p) x hp
  have hd (i : Fin 3) : deriv (fun a => G a i) x = D ξ i := (hasDerivAt_pi.mp HD i).deriv
  have hξu : |ξ 1| ≤ Real.sqrt (p x 1) * |((p x 0 + 1) / phaseNorm (p x 0 + 1) 1) * ξ 0| := by
    rw [Hc.1, Hc.2.1]
    exact hdu
  have hξw : |ξ 2| ≤ Real.sqrt (p x 2) * |((p x 0 + 1) / phaseNorm (p x 0 + 1) 1) * ξ 0| := by
    rw [Hc.1, Hc.2.2]
    exact hdw
  have Hunit (z : ConnectionParameters)
      (hz : ((p x 0 + 1) / phaseNorm (p x 0 + 1) 1) * z 0 = 1)
      (hzu : |z 1| ≤ Real.sqrt (p x 1)) (hzw : |z 2| ≤ Real.sqrt (p x 2)) :=
    connectionReturn_unit_cone hμ hε hsε hεL hu0 hw0 hz hzu hzw
  have Hphase := homogeneous_phase_ratio_of_unit D (fun z hz hzu hzw =>
    (Hunit z hz hzu hzw).2.1) ξ (by rw [Hc.1]; exact ne_of_lt hdf) hξu hξw
  rw [Hc.1] at Hphase
  have hR := (phaseNorm_ratio_bounds (b := 1) (by linarith only [hμ] : 2 ≤ p x 0 + 1) (by norm_num)).1
  have Hcone := homogeneous_cone_of_unit D
    (show 0 < (p x 0 + 1) / phaseNorm (p x 0 + 1) 1 by linarith only [hR])
    (a := Real.sqrt (p x 1)) (b := Real.sqrt (p x 2))
    (A := Real.sqrt (G x 1)) (B := Real.sqrt (G x 2)) (by
      intro z hz hzu hzw
      have Hz := Hunit z hz hzu hzw
      have hd0 : 0 ≤ D z 0 := by linarith only [Hz.1]
      refine ⟨hd0, Hz.2.2.1.trans ?_, Hz.2.2.2.trans ?_⟩
      · change (1 / 3) * Real.sqrt (G x 1) * D z 0 ≤ Real.sqrt (G x 1) * D z 0
        nlinarith only [mul_nonneg (Real.sqrt_nonneg (G x 1)) hd0]
      · have hL : 4 ≤ -Real.log (p x 2) := by
          change 4 ≤ -Real.log (w x)
          have Hl := Real.log_le_log hw0.1 (hw0.2.trans hεL)
          rw [Real.log_exp] at Hl
          linarith only [Hl]
        have hgap := (connection_cone_gap hμ hL).1
        have hgap0 : 0 ≤ 1 - Real.exp (-(-Real.log (p x 2)) / (2 * p x 0)) :=
          (by positivity : (0 : ℝ) ≤ 1 / p x 0).trans hgap
        have Hb := mul_le_mul_of_nonneg_right (show
          1 - (1 - Real.exp (-(-Real.log (p x 2)) / (2 * p x 0))) / 2 ≤ 1 by linarith)
          (mul_nonneg (Real.sqrt_nonneg (G x 2)) hd0)
        change (1 - (1 - Real.exp (-(-Real.log (p x 2)) / (2 * p x 0))) / 2) *
          Real.sqrt (G x 2) * D z 0 ≤ Real.sqrt (G x 2) * D z 0
        nlinarith only [Hb]) ξ hξu hξw
  have hsmall : 1 / (4 * p x 0) ≤ 1 / 4 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    linarith only [hμ]
  have Hbounds : 3 / 4 ≤ D ξ 0 / deriv f x ∧ D ξ 0 / deriv f x ≤ 5 / 4 := by
    have Hb := abs_le.mp (Hphase.trans hsmall)
    constructor <;> linarith only [Hb.1, Hb.2]
  have Hneg : D ξ 0 < 0 := by
    have Hpos : 0 < D ξ 0 / deriv f x := lt_of_lt_of_le (by norm_num) Hbounds.1
    exact (div_pos_iff.mp Hpos).resolve_left (fun h => (not_lt_of_ge hdf.le) h.2) |>.1
  refine ⟨HD.differentiableAt, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [hd]
  · rwa [hd]
  · simpa only [hd] using Hbounds
  · simpa only [hd] using Hcone.1
  · simpa only [hd] using Hcone.2
