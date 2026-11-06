-- Prove2me | solution 1 for BianchiIX.exists_restartShearTail_output_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T05:02:42.563616+00:00
-- url     : https://prove2.me/submissions/7b741def-add0-473d-ad2b-8a8f2f81fa69

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_ShearTransportData
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_Dynamics_EntranceRegion
import Definitions.Def_BianchiIX_Dynamics_ConnectionExistence
import Definitions.Def_BianchiIX_Dynamics_ConnectionEvents
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturn
import Definitions.Def_BianchiIX_Dynamics_EntranceReturn
import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_Dynamics_ConnectionPhysicalReturn
import Definitions.Def_BianchiIX_Dynamics_CoreConnectionChart
import Theorems.Thm_BianchiIX_connectionReturn_restart_bounds
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_entrancePartialCore_reflection_values
import Theorems.Thm_BianchiIX_entranceReturn_active_component
import Theorems.Thm_BianchiIX_entranceReturn_decay
import Theorems.Thm_BianchiIX_entranceReturn_region
import Theorems.Thm_BianchiIX_entranceReturn_regular
import Theorems.Thm_BianchiIX_entrance_phase_bounds
import Theorems.Thm_BianchiIX_exists_common_rpow_budget
import Theorems.Thm_BianchiIX_exists_restartShearFastEntry_control
import Theorems.Thm_BianchiIX_exists_restartShearTail_connection
import Theorems.Thm_BianchiIX_exists_restartShearTail_entrance_inputs
import Theorems.Thm_BianchiIX_exists_restartShearTail_entrance_phase
import Theorems.Thm_BianchiIX_hasDerivAt_normalized_components
import Theorems.Thm_BianchiIX_hasDerivAt_toProjectiveState_normalized
import Theorems.Thm_BianchiIX_le_exp_of_clock_deriv_le
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
import Theorems.Thm_BianchiIX_normalizedMaxCurve_shift
import Theorems.Thm_BianchiIX_normalizedMaxCurve_wall_sign
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_shearTail_constraint_bounds
import Theorems.Thm_BianchiIX_weak_product_directional
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Module
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_sq (m v : ℝ) : coreRadius m v ^ 2 = coreEnergy m v :=
  Real.sq_sqrt (by unfold coreEnergy; positivity)

end
end

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

private theorem BianchiIX.coreAngle_sqrt {m v : ℝ} (hv : 0 < v) :
    Real.sqrt (1 + ((1 - m) / v) ^ 2) = coreRadius m v / v := by
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (div_nonneg (coreRadius_pos hv).le hv.le)).mpr
  simp only [div_pow, coreRadius_sq]
  unfold coreEnergy
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.cosh_coreAngle {m v : ℝ} (hv : 0 < v) :
    Real.cosh (coreAngle m v) = coreRadius m v / v := by
  rw [coreAngle, Real.cosh_arsinh, coreAngle_sqrt hv]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.shearTail_wall_rates {a p s n x y : ℝ}
    (ha : 0 < a ∧ a ≤ 1 / 256) (hp : p < 0)
    (hs : a / 2 ≤ s ∧ s ≤ 3 * a)
    (hn : 0 ≤ n ∧ n ≤ a ^ 2) (hx : 0 ≤ x ∧ x ≤ a ^ 2)
    (hy : 0 ≤ y ∧ y ≤ a / 16) (hc : constraint p s n x y = 1) :
    rateOne p s ≤ -2 ∧ |rateTwo p s| ≤ 6 * a ∧ rateThree p s ≤ -a / 2 := by
  obtain ⟨hQ, _, _, _, hp', hAl, hAu⟩ := shearTail_constraint_bounds ha hp hs hn hx hy hc
  have HC : p ^ 2 + s ^ 2 + curvature n x y = 1 := hc
  have ha2 : a ^ 2 ≤ a / 256 := by nlinarith only [ha.1, ha.2]
  have hs0 : 0 ≤ s := by linarith only [hs.1, ha.1]
  have hr0 := Real.sqrt_nonneg (3 : ℝ)
  have hr2 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hrl : (3 : ℝ) / 2 ≤ Real.sqrt 3 := by nlinarith only [hr0, hr2]
  have hru : Real.sqrt 3 ≤ (7 : ℝ) / 4 := by nlinarith only [hr0, hr2]
  have hRslo := mul_le_mul hrl hs.1 (div_nonneg ha.1.le (by norm_num) : 0 ≤ a / 2) hr0
  have hRshi := mul_le_mul hru hs.2 hs0 (by norm_num : (0 : ℝ) ≤ 7 / 4)
  refine ⟨?_, abs_le.mpr ⟨?_, ?_⟩, ?_⟩
  · dsimp only [rateOne, shearSq]
    nlinarith only [hp', sq_nonneg (p + 15 / 16), sq_nonneg s]
  · dsimp only [rateTwo, shearSq]
    nlinarith only [HC, (abs_le.mp hQ).1, hAu, hRslo, ha2, ha.1]
  · dsimp only [rateTwo, shearSq]
    nlinarith only [HC, (abs_le.mp hQ).2, hAl, hRshi, ha2, ha.1, sq_nonneg a]
  · dsimp only [rateThree, shearSq]
    nlinarith only [HC, (abs_le.mp hQ).2, hAl, hRslo, ha2, ha.1, sq_nonneg a]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.shearTail_shear_rate {a s n x y : ℝ}
    (ha : 0 ≤ a ∧ a ≤ 1 / 256) (hs : |s| ≤ 3 * a)
    (hn : 0 ≤ n) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |shearMinus s n x y| ≤ 3 * (x ^ 2 + y ^ 2 + n * (x + y) + a * n ^ 2) := by
  have hQ : |curvature n x y| ≤ n ^ 2 + x ^ 2 + y ^ 2 + 2 * n * (x + y) := by
    apply abs_le.mpr
    dsimp only [curvature]
    constructor
    · nlinarith only [sq_nonneg n, sq_nonneg (x - y)]
    · nlinarith only [mul_nonneg hx hy, mul_nonneg hn (add_nonneg hx hy)]
  have hH : |-x ^ 2 + y ^ 2 + n * x - n * y| ≤ x ^ 2 + y ^ 2 + n * (x + y) := by
    apply abs_le.mpr
    constructor <;> nlinarith only [sq_nonneg x, sq_nonneg y, mul_nonneg hn hx, mul_nonneg hn hy]
  have hr : |Real.sqrt 3| ≤ (2 : ℝ) := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  have HQ := mul_le_mul hQ hs (abs_nonneg _) (by positivity : 0 ≤ n ^ 2 + x ^ 2 + y ^ 2 + 2 * n * (x + y))
  have HH := mul_le_mul hr hH (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  have H := abs_add_le (curvature n x y * s) (Real.sqrt 3 * (-x ^ 2 + y ^ 2 + n * x - n * y))
  rw [abs_mul, abs_mul] at H
  have Hsmall := mul_nonneg (show 0 ≤ 1 - 6 * a by linarith only [ha.2])
    (show 0 ≤ x ^ 2 + y ^ 2 + n * (x + y) by positivity)
  dsimp only [shearMinus]
  nlinarith only [H, HQ, HH, Hsmall, mul_nonneg ha.1 (add_nonneg (sq_nonneg x) (sq_nonneg y))]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_shearTail_entrance_wall_scale {h q D δ : ℝ}
    (hq : 2 < q) (hD : 2 < D) (hδ : 0 < δ) :
    ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
      a ≤ 1 ∧ (20 * h * a ^ (q - 2) + 80 * a ^ (D / 2 - 1)) * (1 + |Real.log a|) ≤ δ := by
  have Hp (p : ℝ) (hp : 0 < p) :
      Tendsto (fun a : ℝ => a ^ p + |Real.log a * a ^ p|) (𝓝[>] 0) (𝓝 0) := by
    have H : Tendsto (fun a : ℝ => a ^ p) (𝓝[>] 0) (𝓝 0) := by
      simpa only [Real.zero_rpow hp.ne'] using
        (Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto.mono_left nhdsWithin_le_nhds
    simpa only [abs_zero, add_zero] using H.add (tendsto_log_mul_rpow_nhdsGT_zero hp).abs
  have Hn := Hp (q - 2) (by linarith only [hq])
  have Hy := Hp (D / 2 - 1) (by linarith only [hD])
  have H : Tendsto (fun a : ℝ => 20 * h * (a ^ (q - 2) + |Real.log a * a ^ (q - 2)|) +
      80 * (a ^ (D / 2 - 1) + |Real.log a * a ^ (D / 2 - 1)|)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (Hn.const_mul (20 * h)).add (Hy.const_mul 80)
  have HI : Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have HE : ∀ᶠ a : ℝ in 𝓝[>] 0,
      a ≤ 1 ∧ (20 * h * a ^ (q - 2) + 80 * a ^ (D / 2 - 1)) * (1 + |Real.log a|) ≤ δ := by
    filter_upwards [show ∀ᶠ a : ℝ in 𝓝[>] 0, 0 < a from self_mem_nhdsWithin,
      HI.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      H.eventually (gt_mem_nhds hδ)] with a ha ha1 hb
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg ha.le (q - 2)),
      abs_of_nonneg (Real.rpow_nonneg ha.le (D / 2 - 1))] at hb
    exact ⟨ha1.le, by nlinarith only [hb]⟩
  obtain ⟨astar, hastar, HA⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp HE
  exact ⟨astar, hastar, fun a ha => HA ha⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_shearTail_sqrt_wall_scale {h q D δ : ℝ}
    (hh : 0 ≤ h) (hq : 2 < q) (hD : 2 < D) (hδ : 0 < δ) :
    ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
      a ≤ 1 ∧ (1 + |Real.log a|) *
        Real.sqrt (20 * h * a ^ (q - 2) + 80 * a ^ (D / 2 - 1)) ≤ δ := by
  obtain ⟨astar, hastar, HA⟩ := exists_shearTail_entrance_wall_scale
    (h := (20 * h + 1) / 20) (q := q / 2 + 1) (D := D / 2 + 1)
    (by linarith only [hq]) (by linarith only [hD]) hδ
  refine ⟨astar, hastar, ?_⟩
  intro a ha
  obtain ⟨ha1, H⟩ := HA a ha
  let x := a ^ (q / 2 - 1)
  let y := a ^ (D / 4 - 1 / 2)
  have hx : 0 ≤ x := Real.rpow_nonneg ha.1.le _
  have hy : 0 ≤ y := Real.rpow_nonneg ha.1.le _
  have hx2 : x ^ 2 = a ^ (q - 2) := by
    dsimp only [x]
    rw [sq, ← Real.rpow_add ha.1]
    congr 1
    ring
  have hy2 : y ^ 2 = a ^ (D / 2 - 1) := by
    dsimp only [y]
    rw [sq, ← Real.rpow_add ha.1]
    congr 1
    ring
  have Hroot : Real.sqrt (20 * h * a ^ (q - 2) + 80 * a ^ (D / 2 - 1)) ≤
      (20 * h + 1) * x + 80 * y := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [← hx2, ← hy2]
    have Hc : 20 * h ≤ (20 * h + 1) ^ 2 := by nlinarith only [hh, sq_nonneg (20 * h)]
    nlinarith only [mul_le_mul_of_nonneg_right Hc (sq_nonneg x), sq_nonneg y,
      mul_nonneg (mul_nonneg (by positivity : 0 ≤ 20 * h + 1) hx) hy]
  have Heq₁ : q / 2 + 1 - 2 = q / 2 - 1 := by ring
  have Heq₂ : (D / 2 + 1) / 2 - 1 = D / 4 - 1 / 2 := by ring
  rw [Heq₁, Heq₂] at H
  have Hcoef : 20 * ((20 * h + 1) / 20) = 20 * h + 1 := by ring
  rw [Hcoef] at H
  exact ⟨ha1, (mul_le_mul_of_nonneg_left Hroot (by positivity)).trans (by simpa only [mul_comm] using H)⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_shearTail_core_wall_scale {h q D η : ℝ}
    (hh : 0 ≤ h) (hq : 3 < q) (hD : 4 < D) (hη : 0 < η) :
    ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
      a ≤ 1 ∧ 20 * h * a ^ (q - 2) + 80 * a ^ (D / 2 - 1) ≤ η * a / 128 := by
  obtain ⟨astar, hastar, HA⟩ := exists_shearTail_entrance_wall_scale
    (h := h) (q := q - 1) (D := D - 2)
    (by linarith only [hq]) (by linarith only [hD]) (by positivity : 0 < η / 128)
  refine ⟨astar, hastar, ?_⟩
  intro a ha
  obtain ⟨ha1, H⟩ := HA a ha
  let b := 20 * h * a ^ (q - 1 - 2) + 80 * a ^ ((D - 2) / 2 - 1)
  have hb : 0 ≤ b := by dsimp only [b]; positivity [ha.1]
  have Hb : b ≤ η / 128 := by
    have Hmul := mul_le_mul_of_nonneg_left
      (show 1 ≤ 1 + |Real.log a| by linarith only [abs_nonneg (Real.log a)]) hb
    change b * (1 + |Real.log a|) ≤ η / 128 at H
    linarith only [H, Hmul]
  have Heq : b * a = 20 * h * a ^ (q - 2) + 80 * a ^ (D / 2 - 1) := by
    dsimp only [b]
    calc
      _ = 20 * h * (a ^ (q - 1 - 2) * a) + 80 * (a ^ ((D - 2) / 2 - 1) * a) := by ring
      _ = _ := by
        rw [← Real.rpow_add_one ha.1.ne', ← Real.rpow_add_one ha.1.ne']
        rw [show q - 1 - 2 + 1 = q - 2 by ring,
          show (D - 2) / 2 - 1 + 1 = D / 2 - 1 by ring]
  exact ⟨ha1, Heq ▸ (mul_le_mul_of_nonneg_right Hb ha.1.le).trans_eq (by ring)⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreAngle_section_sign (m : ℝ) :
    (coreAngle m 1 < 0 ↔ 1 < m) ∧ (0 < coreAngle m 1 ↔ m < 1) := by
  simp only [coreAngle, div_one, Real.arsinh_neg_iff, Real.arsinh_pos_iff]
  constructor <;> constructor <;> intro h <;> linarith

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.scaled_projective_product_antitone {I : Set ℝ} {Y : ℝ → ProjectiveState} {A : ℝ → ℝ}
    (hI : Convex ℝ I) (hY : ∀ t ∈ I, HasDerivAt Y (A t • projectiveField (Y t)) t)
    (hA : ∀ t ∈ I, 0 ≤ A t)
    (hu : ∀ t ∈ I, 0 ≤ Y t 1 ∧ Y t 1 ≤ 1)
    (hv : ∀ t ∈ I, 0 ≤ Y t 2) (hw : ∀ t ∈ I, 0 ≤ Y t 3) :
    AntitoneOn (fun t => Y t 2 * Y t 3) I := by
  have HD (t : ℝ) (ht : t ∈ I) : HasDerivAt (fun r => Y r 2 * Y r 3)
      (-2 * A t * (1 + coupling (Y t 1) (Y t 2) (Y t 3)) * (Y t 2 * Y t 3)) t := by
    have H := (hasDerivAt_pi.mp (hY t ht) 2).mul (hasDerivAt_pi.mp (hY t ht) 3)
    convert! H using 1
    change _ = A t * activeVelocity (Y t 0) (Y t 1) (Y t 2) (Y t 3) * Y t 3 +
      Y t 2 * (A t * weakVelocity (Y t 0) (Y t 1) (Y t 2) (Y t 3))
    have Heq := weak_product_directional (Y t 0) (Y t 1) (Y t 2) (Y t 3)
    have Hmul := congrArg (fun r => A t * r) Heq
    nlinarith only [Hmul]
  apply antitoneOn_of_deriv_nonpos hI (HasDerivAt.continuousOn HD)
    (fun t ht => (HD t (interior_subset ht)).differentiableAt.differentiableWithinAt)
  intro t ht
  have htI := interior_subset ht
  rw [(HD t htI).deriv]
  have hc : 0 ≤ 1 + coupling (Y t 1) (Y t 2) (Y t 3) := by
    have hu2 := mul_le_mul_of_nonneg_left (hu t htI).2 (hu t htI).1
    dsimp only [coupling]
    nlinarith only [hu2, (hu t htI).2,
      mul_nonneg (hu t htI).1 (add_nonneg (hv t htI) (hw t htI))]
  have H := mul_nonneg (mul_nonneg (hA t htI) hc) (mul_nonneg (hv t htI) (hw t htI))
  nlinarith only [H]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasFDerivAt_normalizedMaxCurve_initial {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    HasFDerivAt (fun y => normalizedMaxCurve y t₀ t) (normalizedFlowDifferential x t₀ t) x := by
  have H := (normalizedMaxCurve_regular ht).2.comp x (contDiffAt_id.prodMk contDiffAt_const)
  exact (H.differentiableAt (by norm_num)).hasFDerivAt

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.le_exp_of_linear_deriv_le {I : Set ℝ} (hI : Convex ℝ I)
    {f f' : ℝ → ℝ} {c s t : ℝ}
    (hf : ∀ u ∈ I, HasDerivAt f (f' u) u) (hbound : ∀ u ∈ I, f' u ≤ c * f u)
    (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) :
    f t ≤ f s * Real.exp (c * (t - s)) := by
  exact le_exp_of_clock_deriv_le hI hf (fun u _ => hasDerivAt_id u)
    (fun u hu => by simpa only [mul_one] using hbound u hu) hs ht hst

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.abs_sub_le_of_deriv_primitive {f f' z z' : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (z' t) t)
    (hb : ∀ t ∈ Icc a b, |f' t| ≤ z' t) :
    ∀ t ∈ Icc a b, |f t - f a| ≤ z t - z a := by
  intro t ht
  have ha : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
  have HU := le_exp_of_linear_deriv_le (convex_Icc a b) (fun s hs => (hf s hs).sub (hz s hs)) (c := 0)
    (fun s hs => by nlinarith only [le_abs_self (f' s), hb s hs]) ha ht ht.1
  have HL := le_exp_of_linear_deriv_le (convex_Icc a b) (fun s hs => (hf s hs).neg.sub (hz s hs)) (c := 0)
    (fun s hs => by nlinarith only [neg_le_abs (f' s), hb s hs]) ha ht ht.1
  simp only [zero_mul, Real.exp_zero, mul_one, Pi.sub_apply, Pi.neg_apply] at HU HL
  exact abs_le.mpr ⟨by linarith only [HL], by linarith only [HU]⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.coreAngle_entry_eq_neg_arcosh {m : ℝ} (hm : 1 < m) :
    coreAngle m 1 = -Real.arcosh (coreRadius m 1) := by
  have H := Real.arcosh_cosh (neg_nonneg.mpr ((coreAngle_section_sign m).1.mpr hm).le)
  rw [Real.cosh_neg, cosh_coreAngle (by norm_num : (0 : ℝ) < 1), div_one] at H
  linarith

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasDerivAt_shearTailDrift {a : ℝ} (ha : a ≠ 0) (A X Y t : ℝ) :
    HasDerivAt (shearTailDrift a A X Y)
      (3 * Y ^ 2 * Real.exp (-a * t) + 3 * X ^ 2 * Real.exp (12 * a * t) +
        a * A / 4 * Real.exp (-2 * t)) t := by
  convert! (((((hasDerivAt_id' t).const_mul (-a)).exp.const_sub 1).const_mul (3 * Y ^ 2 / a)).add
    ((((hasDerivAt_id' t).const_mul (12 * a)).exp.sub_const 1).const_mul (X ^ 2 / (4 * a)))).add
      ((((hasDerivAt_id' t).const_mul (-2)).exp.const_sub 1).const_mul (a * A / 8)) using 1
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.shearTailDrift_le {a A X Y T t : ℝ} (ha : 0 < a) (hA : 0 ≤ A) (ht : t ≤ T) :
    shearTailDrift a A X Y t ≤ 3 * Y ^ 2 / a +
      X ^ 2 / (4 * a) * Real.exp (12 * a * T) + a * A / 8 := by
  have HE := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 12 * a))
  have HX := mul_le_mul_of_nonneg_left HE (by positivity : 0 ≤ X ^ 2 / (4 * a))
  have HY : 0 ≤ 3 * Y ^ 2 / a * Real.exp (-a * t) := by positivity
  have HN : 0 ≤ a * A / 8 * Real.exp (-2 * t) := by positivity
  dsimp only [shearTailDrift]
  nlinarith only [HX, HY, HN, show 0 ≤ X ^ 2 / (4 * a) by positivity]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.shearTail_prefix {a A X Y T : ℝ} {α : ℝ → NormalizedState}
    (ha : 0 < a ∧ a ≤ 1 / 256)
    (hα : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt α (normalizedField (α t)) t)
    (hc : ∀ t ∈ Icc (0 : ℝ) T, stateConstraint (α t) = 1)
    (hn : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ α t 2 ∧ 0 ≤ α t 3 ∧ 0 ≤ α t 4)
    (hregion : ∀ t ∈ Icc (0 : ℝ) T, shearTailRegion a (α t))
    (hinit : α 0 2 ≤ A ∧ α 0 3 ≤ X ∧ α 0 4 ≤ Y) :
    ∀ t ∈ Icc (0 : ℝ) T,
      α t 2 ≤ A * Real.exp (-2 * t) ∧
      α t 3 ≤ X * Real.exp (6 * a * t) ∧
      α t 4 ≤ Y * Real.exp (-(a / 2) * t) ∧
      |α t 1 - α 0 1| ≤ shearTailDrift a A X Y t ∧
      a ^ 2 / 10 ≤ 1 + α t 0 ∧ 1 + α t 0 ≤ 6 * a ^ 2 ∧ α t 0 ≤ -(15 / 16) := by
  have H (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) := hregion t ht
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : α t 0 < 0 := by linarith only [(H t ht).1]
  have HB (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :=
    shearTail_constraint_bounds ha (hp t ht) ⟨(H t ht).2.1, (H t ht).2.2.1⟩
      ⟨(hn t ht).1, (H t ht).2.2.2.1⟩ ⟨(hn t ht).2.1, (H t ht).2.2.2.2.1⟩
      ⟨(hn t ht).2.2, (H t ht).2.2.2.2.2⟩ (hc t ht)
  have HR (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :=
    shearTail_wall_rates ha (hp t ht) ⟨(H t ht).2.1, (H t ht).2.2.1⟩
      ⟨(hn t ht).1, (H t ht).2.2.2.1⟩ ⟨(hn t ht).2.1, (H t ht).2.2.2.2.1⟩
      ⟨(hn t ht).2.2, (H t ht).2.2.2.2.2⟩ (hc t ht)
  have HW (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      α t 2 ≤ A * Real.exp (-2 * t) ∧ α t 3 ≤ X * Real.exp (6 * a * t) ∧
        α t 4 ≤ Y * Real.exp (-(a / 2) * t) := by
    have hz : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
    have HD (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) := hasDerivAt_normalized_components (hα u hu)
    have Hn := le_exp_of_linear_deriv_le (convex_Icc (0 : ℝ) T)
      (fun u hu => (HD u hu).2.2.1)
      (fun u hu => mul_le_mul_of_nonneg_right (HR u hu).1 (hn u hu).1) hz ht ht.1
    have Hx := le_exp_of_linear_deriv_le (convex_Icc (0 : ℝ) T)
      (fun u hu => (HD u hu).2.2.2.1)
      (fun u hu => mul_le_mul_of_nonneg_right ((le_abs_self _).trans (HR u hu).2.1) (hn u hu).2.1) hz ht ht.1
    have Hy := le_exp_of_linear_deriv_le (convex_Icc (0 : ℝ) T)
      (fun u hu => (HD u hu).2.2.2.2)
      (fun u hu => mul_le_mul_of_nonneg_right (HR u hu).2.2 (hn u hu).2.2) hz ht ht.1
    simp only [sub_zero] at Hn Hx Hy
    rw [neg_div] at Hy
    exact ⟨Hn.trans (mul_le_mul_of_nonneg_right hinit.1 (Real.exp_pos _).le),
      Hx.trans (mul_le_mul_of_nonneg_right hinit.2.1 (Real.exp_pos _).le),
      Hy.trans (mul_le_mul_of_nonneg_right hinit.2.2 (Real.exp_pos _).le)⟩
  have HS (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      |shearMinus (α t 1) (α t 2) (α t 3) (α t 4)| ≤
        3 * Y ^ 2 * Real.exp (-a * t) + 3 * X ^ 2 * Real.exp (12 * a * t) +
          a * A / 4 * Real.exp (-2 * t) := by
    have Hs := shearTail_shear_rate ⟨ha.1.le, ha.2⟩
      (abs_le.mpr ⟨by linarith only [(H t ht).2.1, ha.1], (H t ht).2.2.1⟩)
      (hn t ht).1 (hn t ht).2.1 (hn t ht).2.2
    have Hx := pow_le_pow_left₀ (hn t ht).2.1 (HW t ht).2.1 2
    have Hy := pow_le_pow_left₀ (hn t ht).2.2 (HW t ht).2.2 2
    have hxsq : (X * Real.exp (6 * a * t)) ^ 2 = X ^ 2 * Real.exp (12 * a * t) := by
      rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
      congr 2
      ring
    have hysq : (Y * Real.exp (-(a / 2) * t)) ^ 2 = Y ^ 2 * Real.exp (-a * t) := by
      rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
      congr 2
      ring
    rw [hxsq] at Hx
    rw [hysq] at Hy
    have ha2 : a ^ 2 ≤ a / 256 := by nlinarith only [ha.1, ha.2]
    have hcoef : 3 * (α t 3 + α t 4 + a * α t 2) ≤ a / 4 := by
      have Han := mul_le_mul_of_nonneg_left (H t ht).2.2.2.1 ha.1.le
      have Haa := mul_le_mul_of_nonneg_left ha2 ha.1.le
      nlinarith only [Han, Haa, ha2, (H t ht).2.2.2.2.1, (H t ht).2.2.2.2.2]
    have Hcoef := mul_le_mul_of_nonneg_right hcoef (hn t ht).1
    have Hn := mul_le_mul_of_nonneg_left (HW t ht).1 (div_nonneg ha.1.le (by norm_num) : 0 ≤ a / 4)
    nlinarith only [Hs, Hx, Hy, Hcoef, Hn]
  have HG := abs_sub_le_of_deriv_primitive
    (fun t ht => (hasDerivAt_normalized_components (hα t ht)).2.1)
    (fun t _ => hasDerivAt_shearTailDrift ha.1.ne' A X Y t) HS
  intro t ht
  obtain ⟨Hn, Hx, Hy⟩ := HW t ht
  obtain ⟨_, _, _, _, Hp, Hl, Hu⟩ := HB t ht
  refine ⟨Hn, Hx, Hy, ?_, Hl, Hu, Hp⟩
  simpa only [shearTailDrift, mul_zero, Real.exp_zero, sub_self, mul_zero, zero_add, sub_zero] using HG t ht

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.isClosed_shearTailRegion (a : ℝ) : IsClosed {z | shearTailRegion a z} :=
  (isClosed_le (continuous_apply 0) continuous_const).inter
    ((isClosed_le continuous_const (continuous_apply 1)).inter
      ((isClosed_le (continuous_apply 1) continuous_const).inter
        ((isClosed_le (continuous_apply 2) continuous_const).inter
          ((isClosed_le (continuous_apply 3) continuous_const).inter
            (isClosed_le (continuous_apply 4) continuous_const)))))

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalized_shearTail_control {a A X Y T : ℝ} {z : NormalizedState}
    (ha : 0 < a ∧ a ≤ 1 / 256) (hT : 0 ≤ T)
    (hA : 0 ≤ A ∧ A < a ^ 2)
    (hX : 0 ≤ X ∧ X * Real.exp (6 * a * T) < a ^ 2)
    (hY : 0 ≤ Y ∧ Y < a / 16)
    (hc : stateConstraint z = 1) (hp : z 0 < 0)
    (hs : 3 * a / 4 ≤ z 1 ∧ z 1 ≤ 9 * a / 4)
    (hn : 0 ≤ z 2 ∧ 0 ≤ z 3 ∧ 0 ≤ z 4)
    (hinit : z 2 ≤ A ∧ z 3 ≤ X ∧ z 4 ≤ Y) :
    ∀ t ∈ Icc (0 : ℝ) T,
      let w := normalizedMaxCurve z 0 t
      t ∈ normalizedMaxDomain z 0 ∧ shearTailRegion a w ∧
      w 2 ≤ A * Real.exp (-2 * t) ∧ w 3 ≤ X * Real.exp (6 * a * t) ∧
      w 4 ≤ Y * Real.exp (-(a / 2) * t) ∧ |w 1 - z 1| ≤ shearTailDrift a A X Y t ∧
      a ^ 2 / 10 ≤ 1 + w 0 ∧ 1 + w 0 ≤ 6 * a ^ 2 ∧ w 0 ≤ -(15 / 16) := by
  have hbudget : 3 * Y ^ 2 / a + X ^ 2 / (4 * a) * Real.exp (12 * a * T) + a * A / 8 ≤ a / 8 := by
    have HY := pow_le_pow_left₀ hY.1 hY.2.le 2
    have HX := pow_le_pow_left₀ (mul_nonneg hX.1 (Real.exp_pos _).le) hX.2.le 2
    have he : (X * Real.exp (6 * a * T)) ^ 2 = X ^ 2 * Real.exp (12 * a * T) := by
      rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
      congr 2
      ring
    rw [he] at HX
    have HA := mul_le_mul_of_nonneg_left hA.2.le (sq_nonneg a)
    have haSq : a ^ 2 ≤ 1 / 256 := by nlinarith only [ha.1, ha.2]
    have Haa := mul_nonneg (sq_nonneg a) (sub_nonneg.mpr haSq)
    have hid : a * (3 * Y ^ 2 / a + X ^ 2 / (4 * a) * Real.exp (12 * a * T) + a * A / 8) =
        3 * Y ^ 2 + X ^ 2 * Real.exp (12 * a * T) / 4 + a ^ 2 * A / 8 := by
      field_simp [ha.1.ne']
    apply (mul_le_mul_iff_right₀ ha.1).mp
    rw [hid]
    nlinarith only [HY, HX, HA, Haa, sq_nonneg a]
  let α := normalizedMaxCurve z 0
  let S := {t : ℝ | shearTailRegion a (α t)}
  have hα (t : ℝ) (ht : 0 ≤ t) : HasDerivAt α (normalizedField (α t)) t :=
    (normalizedMaxCurve_forward_of_constraint hc ht).1
  have hcon (t : ℝ) (ht : 0 ≤ t) : stateConstraint (α t) = 1 :=
    (normalizedMaxCurve_forward_of_constraint hc ht).2.1
  have hnonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ α t 2 ∧ 0 ≤ α t 3 ∧ 0 ≤ α t 4 :=
    ⟨(normalizedMaxCurve_wall_sign hc ht (0 : Fin 3)).2.mpr hn.1,
      (normalizedMaxCurve_wall_sign hc ht (1 : Fin 3)).2.mpr hn.2.1,
      (normalizedMaxCurve_wall_sign hc ht (2 : Fin 3)).2.mpr hn.2.2⟩
  have hzero : α 0 = z := normalizedMaxCurve_initial z 0
  have hXsmall : X < a ^ 2 := by
    have HE : 1 ≤ Real.exp (6 * a * T) := Real.one_le_exp_iff.mpr (by positivity [ha.1])
    exact (le_mul_of_one_le_right hX.1 HE).trans_lt hX.2
  have hsz : a / 2 ≤ z 1 ∧ z 1 ≤ 3 * a :=
    ⟨by linarith only [hs.1, ha.1], by linarith only [hs.2, ha.1]⟩
  have HB := shearTail_constraint_bounds ha hp hsz ⟨hn.1, hinit.1.trans hA.2.le⟩
    ⟨hn.2.1, hinit.2.1.trans hXsmall.le⟩ ⟨hn.2.2, hinit.2.2.trans hY.2.le⟩ hc
  have hS0 : (0 : ℝ) ∈ S := by
    change shearTailRegion a (α 0)
    rw [hzero]
    exact ⟨by linarith only [HB.2.2.2.2.1], hsz.1, hsz.2,
      hinit.1.trans hA.2.le, hinit.2.1.trans hXsmall.le, hinit.2.2.trans hY.2.le⟩
  have hclosed : IsClosed (S ∩ Icc 0 T) := by
    have H := (HasDerivAt.continuousOn (fun t (ht : t ∈ Icc (0 : ℝ) T) => hα t ht.1)).preimage_isClosed_of_isClosed
      isClosed_Icc (isClosed_shearTailRegion a)
    convert! H using 1
    ext t
    change (shearTailRegion a (α t) ∧ t ∈ Icc 0 T) ↔ (t ∈ Icc 0 T ∧ shearTailRegion a (α t))
    tauto
  have hwhole : Icc (0 : ℝ) T ⊆ S := by
    apply hclosed.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hS0
    intro t ht hbefore
    obtain ⟨Hn, Hx, Hy, Hs, _, _, Hp⟩ := shearTail_prefix ha
      (fun u hu => hα u hu.1) (fun u hu => hcon u hu.1) (fun u hu => hnonneg u hu.1)
      (fun u hu => hbefore hu) (by simpa only [hzero] using hinit) t ⟨ht.1, le_rfl⟩
    have HD := Hs.trans ((shearTailDrift_le ha.1 hA.1 ht.2.le).trans hbudget)
    rw [hzero] at HD
    have Hsl : a / 2 < α t 1 := by linarith only [(abs_le.mp HD).1, hs.1, ha.1]
    have Hsu : α t 1 < 3 * a := by linarith only [(abs_le.mp HD).2, hs.2, ha.1]
    have Hnn : α t 2 < a ^ 2 := Hn.trans_lt
      ((mul_le_of_le_one_right hA.1 (Real.exp_le_one_iff.mpr (by linarith only [ht.1]))).trans_lt hA.2)
    have Hxx : α t 3 < a ^ 2 := Hx.trans_lt
      ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left ht.2.le (by positivity [ha.1] : 0 ≤ 6 * a))) hX.1).trans_lt hX.2)
    have Hyy : α t 4 < a / 16 := Hy.trans_lt
      ((mul_le_of_le_one_right hY.1 (Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (by linarith only [ha.1] : -(a / 2) ≤ 0) ht.1))).trans_lt hY.2)
    have Hpp : α t 0 < -(1 / 2) := by linarith only [Hp]
    have Hcont (i : Fin 5) := (continuous_apply i).continuousAt.comp (hα t ht.1).continuousAt
    have Hev : ∀ᶠ u in 𝓝 t, u ∈ S := by
      filter_upwards [(Hcont 0).eventually (isOpen_Iio.mem_nhds Hpp),
        (Hcont 1).eventually (isOpen_Ioi.mem_nhds Hsl),
        (Hcont 1).eventually (isOpen_Iio.mem_nhds Hsu),
        (Hcont 2).eventually (isOpen_Iio.mem_nhds Hnn),
        (Hcont 3).eventually (isOpen_Iio.mem_nhds Hxx),
        (Hcont 4).eventually (isOpen_Iio.mem_nhds Hyy)] with u hu0 hu1 hu2 hu3 hu4 hu5
      exact ⟨hu0.le, hu1.le, hu2.le, hu3.le, hu4.le, hu5.le⟩
    exact Hev.filter_mono nhdsWithin_le_nhds
  have H := shearTail_prefix ha
    (fun u hu => hα u hu.1) (fun u hu => hcon u hu.1) (fun u hu => hnonneg u hu.1)
    (fun u hu => hwhole hu) (by simpa only [hzero] using hinit)
  intro t ht
  refine ⟨normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht.1, hwhole ht, ?_⟩
  simpa only [hzero] using H t ht

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartSectionChart_constraint {h : ℝ} {Z : RestartCenterState}
    (hZ : 0 ≤ restartSectionRadicand h Z) : stateConstraint (restartSectionChart h Z) = 1 := by
  have H := Real.sq_sqrt hZ
  dsimp [stateConstraint, constraint, shearSq, restartSectionChart]
  rw [neg_sq, H]
  unfold restartSectionRadicand
  ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exp_shearTailTime {a : ℝ} (ha : 0 < a) (c D : ℝ) :
    Real.exp (c * a * shearTailTime a D) = a ^ (-c * D) := by
  rw [Real.rpow_def_of_pos ha]
  congr 1
  dsimp only [shearTailTime]
  rw [one_div, Real.log_inv]
  field_simp

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_shearTail_scale_control {h q D P : ℝ}
    (hh : 0 ≤ h) (hq : 2 < q) (hD : 0 ≤ D) (hP : 6 * D + 2 < P) :
    ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
      ∀ ε ζ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 128) → (0 ≤ ζ ∧ ζ ≤ a ^ P) →
        ∀ z : NormalizedState, stateConstraint z = 1 → z 0 < 0 →
          (3 * a / 4 ≤ z 1 ∧ z 1 ≤ 9 * a / 4) →
          (0 ≤ z 2 ∧ 0 ≤ z 3 ∧ 0 ≤ z 4) →
          (z 2 ≤ h * a ^ q ∧ z 3 ≤ 2 * ζ ∧ z 4 ≤ 4 * ε * a) →
          let T := shearTailTime a D
          0 ≤ T ∧ ∀ t ∈ Icc (0 : ℝ) T,
            let w := normalizedMaxCurve z 0 t
            t ∈ normalizedMaxDomain z 0 ∧ shearTailRegion a w ∧
            w 2 ≤ h * a ^ q * Real.exp (-2 * t) ∧
            w 3 ≤ 2 * ζ * Real.exp (6 * a * t) ∧
            w 4 ≤ 4 * ε * a * Real.exp (-(a / 2) * t) ∧
            |w 1 - z 1| ≤ 48 * ε ^ 2 * a + ζ ^ 2 / a * a ^ (-12 * D) + h * a ^ (q + 1) / 8 ∧
            a ^ 2 / 10 ≤ 1 + w 0 ∧ 1 + w 0 ≤ 6 * a ^ 2 ∧
            toProjectiveState w 2 < 1 := by
  let C : Fin 2 → ℝ := ![h, 40]
  let p : Fin 2 → ℝ := ![q - 2, P - 6 * D - 2]
  obtain ⟨astar, hastar, hastar', HB⟩ := exists_common_rpow_budget
    (C := C) (p := p) (ε := fun _ => (1 : ℝ) / 2) Finset.univ
    (fun i _ => by fin_cases i; exact hh; norm_num [C])
    (fun i _ => by fin_cases i; dsimp [p]; linarith only [hq]; dsimp [p]; linarith only [hP])
    (fun _ _ => by norm_num) (show (0 : ℝ) < 1 / 256 by norm_num)
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε ζ hε hζ z hc hp hs hn hinit T
  have haSmall : a ≤ 1 / 256 := ha.2.trans hastar'.le
  have HN : h * a ^ (q - 2) < 1 / 2 := HB a ha 0 (Finset.mem_univ _)
  have HX : 40 * a ^ (P - 6 * D - 2) < 1 / 2 := HB a ha 1 (Finset.mem_univ _)
  have hR : 0 ≤ a ^ (P - 6 * D - 2) := Real.rpow_nonneg ha.1.le _
  have hNid : h * a ^ q = (h * a ^ (q - 2)) * a ^ 2 := by
    rw [Real.rpow_sub ha.1, Real.rpow_two]
    field_simp [ha.1.ne']
  have hXid : a ^ P * a ^ (-6 * D) = a ^ (P - 6 * D - 2) * a ^ 2 := by
    rw [← Real.rpow_two a, ← Real.rpow_add ha.1, ← Real.rpow_add ha.1]
    congr 1
    ring
  have hA : 0 ≤ h * a ^ q ∧ h * a ^ q < a ^ 2 := by
    refine ⟨mul_nonneg hh (Real.rpow_nonneg ha.1.le _), ?_⟩
    rw [hNid]
    have H := mul_lt_mul_of_pos_right HN (sq_pos_of_pos ha.1)
    nlinarith only [H, sq_pos_of_pos ha.1]
  have hXtotal : 2 * ζ * Real.exp (6 * a * T) < a ^ 2 / 40 := by
    change 2 * ζ * Real.exp (6 * a * shearTailTime a D) < _
    rw [exp_shearTailTime ha.1 6 D]
    have H := mul_le_mul_of_nonneg_right hζ.2 (Real.rpow_nonneg ha.1.le (-6 * D))
    rw [hXid] at H
    have H' := mul_lt_mul_of_pos_right HX (sq_pos_of_pos ha.1)
    nlinarith only [H, H']
  have hX : 0 ≤ 2 * ζ ∧ 2 * ζ * Real.exp (6 * a * T) < a ^ 2 :=
    ⟨by linarith only [hζ.1], hXtotal.trans (by nlinarith only [sq_pos_of_pos ha.1])⟩
  have hY : 0 ≤ 4 * ε * a ∧ 4 * ε * a < a / 16 := by
    have H := mul_le_mul_of_nonneg_right hε.2 ha.1.le
    exact ⟨mul_nonneg (by linarith only [hε.1]) ha.1.le, by linarith only [H, ha.1]⟩
  have hT : 0 ≤ T := mul_nonneg (div_nonneg hD ha.1.le)
    (Real.log_nonneg ((le_div_iff₀ ha.1).mpr (by linarith only [haSmall])))
  have H := normalized_shearTail_control ⟨ha.1, haSmall⟩ hT hA hX hY hc hp hs hn hinit
  refine ⟨hT, ?_⟩
  intro t ht w
  obtain ⟨Hdom, Hreg, Hn, Hx, Hy, Hs, HAl, HAu, _⟩ := H t ht
  have Hdrift := Hs.trans (shearTailDrift_le ha.1 hA.1 ht.2)
  have Hid : 3 * (4 * ε * a) ^ 2 / a + (2 * ζ) ^ 2 / (4 * a) * Real.exp (12 * a * T) +
      a * (h * a ^ q) / 8 = 48 * ε ^ 2 * a + ζ ^ 2 / a * a ^ (-12 * D) + h * a ^ (q + 1) / 8 := by
    change _ + _ * Real.exp (12 * a * shearTailTime a D) + _ = _
    rw [exp_shearTailTime ha.1 12 D, Real.rpow_add ha.1, Real.rpow_one]
    field_simp [ha.1.ne']
    ring
  refine ⟨Hdom, Hreg, Hn, Hx, Hy, Hdrift.trans_eq Hid, HAl, HAu, ?_⟩
  have hApos : 0 < 1 + w 0 := (div_pos (sq_pos_of_pos ha.1) (by norm_num)).trans_le HAl
  have hx0 : 0 ≤ w 3 := (normalizedMaxCurve_wall_sign hc ht.1 (1 : Fin 3)).2.mpr hn.2.1
  have hxsmall : w 3 < a ^ 2 / 40 := Hx.trans_lt
    ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left ht.2 (by positivity [ha.1] : 0 ≤ 6 * a))) hX.1).trans_lt hXtotal)
  have hr : Real.sqrt (3 : ℝ) ≤ 2 := by
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  change Real.sqrt 3 * w 3 / (1 + w 0) < 1
  apply (div_lt_one hApos).mpr
  have Hr := mul_le_mul_of_nonneg_right hr hx0
  nlinarith only [Hr, hxsmall, HAl, sq_pos_of_pos ha.1]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.shearTail_projectiveCoordinate_le {a p v B : ℝ}
    (ha : 0 < a) (hA : a ^ 2 / 10 ≤ 1 + p) (hv : 0 ≤ v ∧ v ≤ B) :
    0 ≤ projectiveCoord p v ∧ projectiveCoord p v ≤ 20 * B / a ^ 2 := by
  have hApos : 0 < 1 + p := (div_pos (sq_pos_of_pos ha) (by norm_num)).trans_le hA
  have hB : 0 ≤ B := hv.1.trans hv.2
  have hr : Real.sqrt (3 : ℝ) ≤ 2 := by
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  refine ⟨div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hv.1) hApos.le, ?_⟩
  change Real.sqrt 3 * v / (1 + p) ≤ _
  calc
    _ ≤ 2 * B / (a ^ 2 / 10) := div_le_div₀ (by positivity : 0 ≤ 2 * B)
      (mul_le_mul hr hv.2 hv.1 (by norm_num)) (by positivity) hA
    _ = _ := by ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.shearTail_projective_endpoint {a h q D ε ζ : ℝ} {z : NormalizedState}
    (ha : 0 < a ∧ a ≤ 1) (hh : 0 ≤ h) (hD : 0 ≤ D)
    (hA : a ^ 2 / 10 ≤ 1 + z 0)
    (hn : 0 ≤ z 2 ∧ 0 ≤ z 3 ∧ 0 ≤ z 4)
    (hwall : z 2 ≤ h * a ^ q * Real.exp (-2 * shearTailTime a D) ∧
      z 3 ≤ 2 * ζ * Real.exp (6 * a * shearTailTime a D) ∧
      z 4 ≤ 4 * ε * a * Real.exp (-(a / 2) * shearTailTime a D)) :
    0 ≤ toProjectiveState z 1 ∧ toProjectiveState z 1 ≤ 20 * h * a ^ (q - 2) ∧
    0 ≤ toProjectiveState z 2 ∧ toProjectiveState z 2 ≤ 40 * ζ * a ^ (-6 * D - 2) ∧
    0 ≤ toProjectiveState z 3 ∧ toProjectiveState z 3 ≤ 80 * ε * a ^ (D / 2 - 1) := by
  have hT : 0 ≤ shearTailTime a D := mul_nonneg (div_nonneg hD ha.1.le)
    (Real.log_nonneg ((le_div_iff₀ ha.1).mpr (by simpa only [one_mul] using ha.2)))
  have Hn : z 2 ≤ h * a ^ q := hwall.1.trans
    (mul_le_of_le_one_right (mul_nonneg hh (Real.rpow_nonneg ha.1.le _))
      (Real.exp_le_one_iff.mpr (by linarith only [hT])))
  have Hx := hwall.2.1
  rw [exp_shearTailTime ha.1 6 D] at Hx
  have he : Real.exp (-(a / 2) * shearTailTime a D) = a ^ (D / 2) := by
    convert! exp_shearTailTime ha.1 (-(1 / 2)) D using 1 <;> congr 1 <;> ring
  have Hy := hwall.2.2
  rw [he] at Hy
  obtain ⟨Hn0, Hn1⟩ := shearTail_projectiveCoordinate_le ha.1 hA ⟨hn.1, Hn⟩
  obtain ⟨Hx0, Hx1⟩ := shearTail_projectiveCoordinate_le ha.1 hA ⟨hn.2.1, Hx⟩
  obtain ⟨Hy0, Hy1⟩ := shearTail_projectiveCoordinate_le ha.1 hA ⟨hn.2.2, Hy⟩
  refine ⟨Hn0, Hn1.trans_eq ?_, Hx0, Hx1.trans_eq ?_, Hy0, Hy1.trans_eq ?_⟩
  · rw [Real.rpow_sub ha.1, Real.rpow_two]
    ring
  · rw [Real.rpow_sub ha.1, Real.rpow_two]
    ring
  · rw [Real.rpow_sub ha.1, Real.rpow_one]
    field_simp [ha.1.ne']
    ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.partialCoreEntry_region {y : ProjectiveState} {ε : ℝ}
    (hk : 6 ≤ coreRadius (y 0) (y 2)) (hv : 1 ≤ y 2)
    (hu : 0 ≤ y 1) (hp : 0 ≤ y 2 * y 3)
    (hε : ε ≤ 1 / 10000)
    (hsmall : y 1 + y 2 * y 3 ≤ ε / coreRadius (y 0) (y 2)) :
    coreRegion (coreRadius (y 0) (y 2)) y := by
  have hk0 : 0 < coreRadius (y 0) (y 2) := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 6) hk
  have Hcap := hsmall.trans (div_le_div_of_nonneg_right hε hk0.le)
  refine ⟨?_, hv, ⟨hu, ?_⟩, ⟨hp, ?_⟩⟩
  · rw [coreRadius_sq, sub_self, abs_zero]
    norm_num
  · linarith only [Hcap, hp]
  · linarith only [Hcap, hu]

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

private theorem BianchiIX.contDiffAt_restartSectionChart {h : ℝ} {Z : RestartCenterState}
    (hZ : 0 < restartSectionRadicand h Z) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k (restartSectionChart h) Z := by
  have hr : ContDiff ℝ k (restartSectionRadicand h) := by
    unfold restartSectionRadicand curvature
    fun_prop
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · exact (hr.contDiffAt.sqrt hZ.ne').neg
  · exact contDiffAt_apply ℝ ℝ (0 : Fin 3) Z
  · exact contDiffAt_const
  · exact contDiffAt_apply ℝ ℝ (1 : Fin 3) Z
  · exact contDiffAt_apply ℝ ℝ (2 : Fin 3) Z

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.entranceReturn_walls_nonincreasing {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) :
    entranceReturnState y 1 ≤ y 1 ∧ entranceReturnState y 3 ≤ y 3 := by
  have H := entranceReturn_decay hk hm hu hv hw
  have hk0 : 0 < coreRadius (y 0) (y 2) := by linarith only [hk]
  have hL : 0 ≤ -Real.log (y 2) := neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le)
  have hEs : Real.exp (-coreRadius (y 0) (y 2) * -Real.log (y 2) / 3) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk0.le) hL) (by norm_num))
  have hEw : Real.exp (-(-Real.log (y 2)) / coreRadius (y 0) (y 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hL) hk0.le)
  constructor
  · exact H.1.trans ((mul_le_mul_of_nonneg_left hEs (mul_nonneg hu.1 hv.1.le)).trans
      (by nlinarith only [mul_le_mul_of_nonneg_left hv.2.le hu.1]))
  · exact H.2.trans ((mul_le_mul_of_nonneg_left hEw (mul_nonneg hw.1 hv.1.le)).trans
      (by nlinarith only [mul_le_mul_of_nonneg_left hv.2.le hw.1]))

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.entranceReturn_partialCore_entry {y : ProjectiveState} {η : ℝ}
    (hk : 8 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) (hη : 0 < η ∧ η ≤ 1 / 10000)
    (hsmall : y 1 + y 2 * y 3 ≤ η / (2 * coreRadius (y 0) (y 2))) :
    let k := coreRadius (y 0) (y 2)
    let z := entranceReturnState y
    let κ := coreRadius (z 0) (z 2)
    6 ≤ κ ∧ (99 / 100 * k ≤ κ ∧ κ ≤ 101 / 100 * k) ∧
      z 2 = 1 ∧ 1 < z 0 ∧ coreRegion κ z ∧
      (0 ≤ z 1 ∧ z 1 ≤ y 1) ∧ (0 ≤ z 3 ∧ z 3 ≤ y 2 * y 3) ∧
      z 1 + z 2 * z 3 ≤ η / κ ∧ projectiveCoreAngle z = -Real.arcosh κ := by
  intro k z κ
  have hk' : 7 / 4 ≤ k := by linarith only [hk]
  have hk0 : 0 < k := by linarith only [hk]
  have HE := (entranceReturn_regular hk' hm hu hv hw).1
  have HR := entranceReturn_region hk' hm hu hv hw _ ⟨HE.1.1.1.le, le_rfl⟩
  change entranceRegion k z at HR
  have hκ : 99 / 100 * k ≤ κ ∧ κ ≤ 101 / 100 * k := by
    have H := abs_le.mp HR.2.1
    change - (k / 100) ≤ κ - k ∧ κ - k ≤ k / 100 at H
    constructor <;> linarith only [H.1, H.2]
  have hκ6 : 6 ≤ κ := by linarith only [hk, hκ.1]
  have hκ0 : 0 < κ := by linarith only [hκ6]
  have hhit : z 2 = 1 := (entranceReturn_active_component hk' hm hu hv hw).1
  have hm' : 1 < z 0 := by
    have H := (entranceRegion_phase hk' HR).1
    linarith only [H, hk]
  have hU := (entranceReturn_walls_nonincreasing hk' hm hu hv hw).1
  have hL : 0 ≤ -Real.log (y 2) := neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le)
  have hExp : Real.exp (-(-Real.log (y 2)) / k) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hL) hk0.le)
  have hW : z 3 ≤ y 2 * y 3 := (entranceReturn_decay hk' hm hu hv hw).2.trans
    ((mul_le_of_le_one_right (mul_nonneg hw.1 hv.1.le) hExp).trans_eq (mul_comm _ _))
  have hsum : z 1 + z 2 * z 3 ≤ η / κ := by
    rw [hhit, one_mul]
    exact (add_le_add hU hW).trans (hsmall.trans
      (div_le_div_of_nonneg_left hη.1.le hκ0 (by linarith only [hκ.2, hk0])))
  have hprod : 0 ≤ z 2 * z 3 := mul_nonneg HR.2.2.2.1.1 HR.2.2.2.2.1
  refine ⟨hκ6, hκ, hhit, hm', partialCoreEntry_region hκ6 (by rw [hhit])
    HR.2.2.1.1 hprod hη.2 hsum, ⟨HR.2.2.1.1, hU⟩, ⟨HR.2.2.2.2.1, hW⟩, hsum, ?_⟩
  change coreAngle (z 0) (z 2) = -Real.arcosh (coreRadius (z 0) (z 2))
  rw [hhit]
  exact coreAngle_entry_eq_neg_arcosh hm'

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionHeight_of_constraint {x : NormalizedState}
    (hc : stateConstraint x = 1) (hp : x 0 < 0) :
    restartProjectionHeight (x 2, ![x 1, x 3, x 4]) = 1 + x 0 := by
  have hd : restartProjectionDefect (x 2, ![x 1, x 3, x 4]) = 1 - (x 0) ^ 2 := by
    change (x 1) ^ 2 + curvature (x 2) (x 3) (x 4) = _
    dsimp only [stateConstraint, constraint, shearSq] at hc
    linarith only [hc]
  have hden : 1 - x 0 ≠ 0 := by linarith only [hp]
  rw [restartProjectionHeight, hd, show 1 - (1 - (x 0) ^ 2) = (x 0) ^ 2 by ring,
    Real.sqrt_sq_eq_abs, abs_of_neg hp]
  change (1 - x 0 ^ 2) / (1 - x 0) = 1 + x 0
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_restartProjectionDefect {p : ℝ → RestartRadialState}
    {v : RestartRadialState} {t : ℝ} (H : HasDerivAt p v t) :
    HasDerivAt (fun x => restartProjectionDefect (p x))
      (restartProjectionDefectTangent (p t) v) t := by
  have Hn : HasDerivAt (fun x => (p x).1) v.1 t :=
    (ContinuousLinearMap.fst ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt t H
  have Hc (i : Fin 3) : HasDerivAt (fun x => (p x).2 i) (v.2 i) t := by
    let P : RestartCenterState →L[ℝ] ℝ := ContinuousLinearMap.proj i
    exact P.hasFDerivAt.comp_hasDerivAt t
      ((ContinuousLinearMap.snd ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt t H)
  have HD := ((Hc 0).pow 2).add
    ((((Hn.pow 2).add ((Hc 1).pow 2)).add ((Hc 2).pow 2)).const_mul 2)
  have HD' := HD.sub (((Hn.add (Hc 1)).add (Hc 2)).pow 2)
  convert! HD' using 1
  · funext x
    dsimp [restartProjectionDefect, curvature]
    ring
  · dsimp [restartProjectionDefectTangent]
    ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.restartProjectionDefectTangent_bound {p v : RestartRadialState} {R D : ℝ}
    (hp : ‖p‖ ≤ R) (hv : ‖v‖ ≤ D) :
    |restartProjectionDefectTangent p v| ≤ 32 * R * D := by
  have hR : 0 ≤ R := (norm_nonneg p).trans hp
  have hD : 0 ≤ D := (norm_nonneg v).trans hv
  have pn : |p.1| ≤ R := (norm_fst_le p).trans hp
  have pc (i : Fin 3) : |p.2 i| ≤ R := (norm_le_pi_norm p.2 i).trans ((norm_snd_le p).trans hp)
  have vn : |v.1| ≤ D := (norm_fst_le v).trans hv
  have vc (i : Fin 3) : |v.2 i| ≤ D := (norm_le_pi_norm v.2 i).trans ((norm_snd_le v).trans hv)
  have ps : |p.1 + p.2 1 + p.2 2| ≤ 3 * R :=
    ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans (by linarith only [pn, pc 1, pc 2])
  have vs : |v.1 + v.2 1 + v.2 2| ≤ 3 * D :=
    ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans (by linarith only [vn, vc 1, vc 2])
  have Hsum : |p.1 * v.1 + p.2 1 * v.2 1 + p.2 2 * v.2 2| ≤ 3 * R * D := by
    calc
      _ ≤ |p.1 * v.1| + |p.2 1 * v.2 1| + |p.2 2 * v.2 2| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ R * D + R * D + R * D := by
        simp only [abs_mul]
        gcongr
        · exact pc 1
        · exact vc 1
        · exact pc 2
        · exact vc 2
      _ = _ := by ring
  unfold restartProjectionDefectTangent
  calc
    _ ≤ |2 * p.2 0 * v.2 0| + |4 * (p.1 * v.1 + p.2 1 * v.2 1 + p.2 2 * v.2 2)| +
        |2 * (p.1 + p.2 1 + p.2 2) * (v.1 + v.2 1 + v.2 2)| := by
      have HT : |2 * p.2 0 * v.2 0 + 4 * (p.1 * v.1 + p.2 1 * v.2 1 + p.2 2 * v.2 2) -
          2 * (p.1 + p.2 1 + p.2 2) * (v.1 + v.2 1 + v.2 2)| ≤
          |2 * p.2 0 * v.2 0 + 4 * (p.1 * v.1 + p.2 1 * v.2 1 + p.2 2 * v.2 2)| +
          |2 * (p.1 + p.2 1 + p.2 2) * (v.1 + v.2 1 + v.2 2)| := by
        simpa using (abs_sub_le (2 * p.2 0 * v.2 0 + 4 *
          (p.1 * v.1 + p.2 1 * v.2 1 + p.2 2 * v.2 2)) 0
          (2 * (p.1 + p.2 1 + p.2 2) * (v.1 + v.2 1 + v.2 2)))
      exact HT.trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 2 * R * D + 4 * (3 * R * D) + 2 * (3 * R) * (3 * D) := by
      norm_num only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      gcongr
      · exact pc 0
      · exact vc 0
    _ = _ := by ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.restartProjectionHeight_eq_sqrt {p : RestartRadialState}
    (hd : restartProjectionDefect p ≤ 1) :
    restartProjectionHeight p = 1 - Real.sqrt (1 - restartProjectionDefect p) := by
  have Hsq := Real.sq_sqrt (by linarith only [hd] : 0 ≤ 1 - restartProjectionDefect p)
  apply (div_eq_iff (by positivity : 1 + Real.sqrt (1 - restartProjectionDefect p) ≠ 0)).mpr
  nlinarith only [Hsq]

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_restartProjectionHeight {p : ℝ → RestartRadialState}
    {v : RestartRadialState} {t : ℝ} (H : HasDerivAt p v t)
    (hd : restartProjectionDefect (p t) < 1) :
    HasDerivAt (fun x => restartProjectionHeight (p x))
      (restartProjectionDefectTangent (p t) v / (2 * Real.sqrt (1 - restartProjectionDefect (p t)))) t := by
  have HD := hasDerivAt_restartProjectionDefect H
  have HS := ((HD.const_sub 1).sqrt (by linarith only [hd] : 1 - restartProjectionDefect (p t) ≠ 0)).const_sub 1
  have Heq : (fun x => restartProjectionHeight (p x)) =ᶠ[𝓝 t]
      fun x => 1 - Real.sqrt (1 - restartProjectionDefect (p x)) := by
    filter_upwards [HD.continuousAt.eventually (isOpen_Iio.mem_nhds hd)] with x hx
    exact restartProjectionHeight_eq_sqrt hx.le
  convert! HS.congr_of_eventuallyEq Heq using 1
  ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.restartProjectionHeight_derivative_bound {p : ℝ → RestartRadialState}
    {v : RestartRadialState} {t R D : ℝ} (H : HasDerivAt p v t)
    (hd : restartProjectionDefect (p t) ≤ 1 / 2) (hp : ‖p t‖ ≤ R) (hv : ‖v‖ ≤ D) :
    DifferentiableAt ℝ (fun x => restartProjectionHeight (p x)) t ∧
      |deriv (fun x => restartProjectionHeight (p x)) t| ≤ 32 * R * D := by
  have HD := hasDerivAt_restartProjectionHeight H (by linarith only [hd])
  refine ⟨HD.differentiableAt, ?_⟩
  rw [HD.deriv, abs_div, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.sqrt (1 - restartProjectionDefect (p t)))]
  have hsqrt : 1 / 2 ≤ Real.sqrt (1 - restartProjectionDefect (p t)) := by
    have Hsq := Real.sq_sqrt (by linarith only [hd] : 0 ≤ 1 - restartProjectionDefect (p t))
    nlinarith only [Hsq, Real.sqrt_nonneg (1 - restartProjectionDefect (p t)), hd]
  exact (div_le_self (abs_nonneg _) (by linarith only [hsqrt])).trans
    (restartProjectionDefectTangent_bound hp hv)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionDefect_shear_bounds {p : RestartRadialState} {a σ : ℝ}
    (ha : 0 < a ∧ a ≤ 1 / 128) (hσ : |σ| = 1)
    (hs : 3 * a / 4 ≤ σ * p.2 0 ∧ σ * p.2 0 ≤ 9 * a / 4)
    (hn : 0 ≤ p.1 ∧ p.1 ≤ a ^ 2)
    (h₂ : 0 ≤ p.2 1 ∧ p.2 1 ≤ a / 16) (h₃ : 0 ≤ p.2 2 ∧ p.2 2 ≤ a / 16) :
    a ^ 2 / 2 ≤ restartProjectionDefect p ∧ restartProjectionDefect p ≤ 6 * a ^ 2 := by
  have hsig : σ ^ 2 = 1 := by nlinarith only [sq_abs σ, hσ]
  have hsq : (σ * p.2 0) ^ 2 = (p.2 0) ^ 2 := by rw [mul_pow, hsig, one_mul]
  have hslo := pow_le_pow_left₀ (by positivity [ha.1] : 0 ≤ 3 * a / 4) hs.1 2
  have hshi := pow_le_pow_left₀ (by linarith only [hs.1, ha.1] : 0 ≤ σ * p.2 0) hs.2 2
  rw [hsq] at hslo hshi
  have hsum : p.2 1 + p.2 2 ≤ a / 8 := by linarith only [h₂.2, h₃.2]
  have hcross := mul_le_mul hn.2 hsum (add_nonneg h₂.1 h₃.1) (sq_nonneg a)
  have ha1 : a ≤ 1 := by linarith only [ha.2]
  have ha3 : a ^ 2 * a ≤ a ^ 2 := by simpa only [mul_one] using mul_le_mul_of_nonneg_left ha1 (sq_nonneg a)
  have hnsq := pow_le_pow_left₀ hn.1 hn.2 2
  have hdiff : |p.2 1 - p.2 2| ≤ a / 16 :=
    abs_le.mpr ⟨by linarith only [h₂.1, h₃.2], by linarith only [h₃.1, h₂.2]⟩
  have hdsq := pow_le_pow_left₀ (abs_nonneg _) hdiff 2
  rw [sq_abs] at hdsq
  have heq : restartProjectionDefect p = (p.2 0) ^ 2 + p.1 ^ 2 + (p.2 1 - p.2 2) ^ 2 -
      2 * p.1 * (p.2 1 + p.2 2) := by unfold restartProjectionDefect curvature; ring
  constructor
  · rw [heq]
    have ha3small := mul_le_mul_of_nonneg_left ha.2 (sq_nonneg a)
    nlinarith only [hslo, hcross, ha3small, sq_nonneg p.1, sq_nonneg (p.2 1 - p.2 2), sq_nonneg a]
  · rw [heq]
    have hneg := mul_nonneg hn.1 (add_nonneg h₂.1 h₃.1)
    have hnsmall := mul_le_mul_of_nonneg_left ha.2 ha.1.le
    have hn4small := mul_le_mul_of_nonneg_left hnsmall (sq_nonneg a)
    nlinarith only [hshi, hnsq, hn4small, hdsq, hneg, ha3, sq_nonneg a]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionHeight_shear_bounds {p : RestartRadialState} {a σ : ℝ}
    (ha : 0 < a ∧ a ≤ 1 / 128) (hσ : |σ| = 1)
    (hs : 3 * a / 4 ≤ σ * p.2 0 ∧ σ * p.2 0 ≤ 9 * a / 4)
    (hn : 0 ≤ p.1 ∧ p.1 ≤ a ^ 2)
    (h₂ : 0 ≤ p.2 1 ∧ p.2 1 ≤ a / 16) (h₃ : 0 ≤ p.2 2 ∧ p.2 2 ≤ a / 16) :
    restartProjectionDefect p ≤ 1 / 2 ∧
      a ^ 2 / 4 ≤ restartProjectionHeight p ∧ restartProjectionHeight p ≤ 6 * a ^ 2 := by
  obtain ⟨Hlo, Hhi⟩ := restartProjectionDefect_shear_bounds ha hσ hs hn h₂ h₃
  have hd0 : 0 ≤ restartProjectionDefect p := le_trans (by positivity) Hlo
  have hd1 : restartProjectionDefect p ≤ 1 / 2 := by nlinarith only [Hhi, ha.1, ha.2]
  have hsqrt := Real.sqrt_nonneg (1 - restartProjectionDefect p)
  have hsqrt1 : Real.sqrt (1 - restartProjectionDefect p) ≤ 1 := by rw [Real.sqrt_le_one]; linarith only [hd0]
  have hden : 0 < 1 + Real.sqrt (1 - restartProjectionDefect p) := by positivity
  refine ⟨hd1, (le_div_iff₀ hden).mpr ?_, (div_le_iff₀ hden).mpr ?_⟩
  · nlinarith only [Hlo, mul_le_mul_of_nonneg_left hsqrt1 (sq_nonneg a)]
  · nlinarith only [Hhi, mul_nonneg (sq_nonneg a) hsqrt]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasDerivAt_restartShearCurve (σ n₂ n₃ ρ : ℝ) :
    HasDerivAt (restartShearCurve σ n₂ n₃) (restartShearDirection σ) ρ := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [restartShearCurve, restartShearDirection] using (hasDerivAt_id ρ).const_mul σ
  · convert! hasDerivAt_const ρ n₂ using 1
  · convert! hasDerivAt_const ρ n₃ using 1

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.eventually_restartSectionProjectionHeight_eq {h T : ℝ} {Z : RestartCenterState}
    (hrad : 0 < restartSectionRadicand h Z) (hT : 0 ≤ T)
    (hneg : normalizedMaxCurve (restartSectionChart h Z) 0 T 0 < 0) :
    (fun W => restartProjectionHeight (restartSectionRadialState h T W)) =ᶠ[𝓝 Z]
      (fun W => 1 + normalizedMaxCurve (restartSectionChart h W) 0 T 0) := by
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint (restartSectionChart_constraint hrad.le) 0 hT
  have Hchart := (contDiffAt_restartSectionChart hrad 1).continuousAt
  have Hflow := (hasFDerivAt_normalizedMaxCurve_initial hdom).continuousAt.comp Hchart
  have Hcoord : ContinuousAt (fun W => normalizedMaxCurve (restartSectionChart h W) 0 T 0) Z :=
    (continuous_apply 0).continuousAt.comp Hflow
  have HR : ContinuousAt (restartSectionRadicand h) Z := by
    unfold restartSectionRadicand curvature
    fun_prop
  filter_upwards [HR.eventually (isOpen_Ioi.mem_nhds hrad),
    Hcoord.eventually (isOpen_Iio.mem_nhds hneg)] with W hW hN
  have HC := (normalizedMaxCurve_forward_of_constraint (restartSectionChart_constraint hW.le) hT).2.1
  exact restartProjectionHeight_of_constraint HC hN

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_restartFastShearProjectiveEntry_bounds :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q : ℝ, 2 < q →
      ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε σ n₂ n₃ : ℝ,
        (0 ≤ ε ∧ ε ≤ 1 / 64) → |σ| = 1 →
        (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
          let T := q / 2 * Real.log (1 / a)
          let y := restartFastShearProjectiveEntry h T σ n₂ n₃ ρ
          T ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve σ n₂ n₃ ρ)) 0 ∧
          DifferentiableAt ℝ (restartFastShearProjectiveEntry h T σ n₂ n₃) ρ ∧
          DifferentiableAt ℝ (restartFastShearHeight h T σ n₂ n₃) ρ ∧
          a ^ 2 / 4 ≤ restartFastShearHeight h T σ n₂ n₃ ρ ∧
          restartFastShearHeight h T σ n₂ n₃ ρ ≤ 6 * a ^ 2 ∧
          |deriv (restartFastShearHeight h T σ n₂ n₃) ρ| ≤ 512 * a ∧
          (1 / (8 * a) ≤ σ * y 0 ∧ σ * y 0 ≤ 18 / a) ∧
          (0 < y 1 ∧ y 1 ≤ 8 * h * a ^ (q - 2)) ∧
          (n₂ / (12 * a ^ 2) ≤ y 2 ∧ y 2 ≤ 16 * n₂ / a ^ 2) ∧
          (n₃ / (12 * a ^ 2) ≤ y 3 ∧ y 3 ≤ 16 * n₃ / a ^ 2) ∧
          (0 ≤ y 2 + y 3 ∧ y 2 + y 3 ≤ 64 * ε / a) ∧
          (0 ≤ y 2 * y 3 ∧ y 2 * y 3 ≤ 256 * n₂ * n₃ / a ^ 4) := by
  obtain ⟨C, _, h₀, hh₀, H₀⟩ := exists_restartShearFastEntry_control
  refine ⟨min h₀ 1, lt_min hh₀ (by norm_num), ?_⟩
  intro h hh q hq
  obtain ⟨astar, hastar, Ha⟩ := H₀ h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q hq
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε σ n₂ n₃ hε hσ h₂ h₃ ρ hρ T y
  let Z := restartShearCurve σ n₂ n₃ ρ
  let x := normalizedMaxCurve (restartSectionChart h Z) 0 T
  let p := restartSectionRadialState h T Z
  obtain ⟨ha1, hasmall, hT, hrad, hdom, _, hneg, Hcurve, hnpos, hnexp, hshear, hc, hv, _, hw⟩ :=
    Ha a ha ε σ n₂ n₃ hε hσ h₂ h₃ ρ hρ
  change 0 < x 2 at hnpos
  change x 2 ≤ h * a ^ q at hnexp
  change 3 * a / 4 ≤ σ * x 1 ∧ σ * x 1 ≤ 9 * a / 4 at hshear
  have hnsq : p.1 ≤ a ^ 2 := hnexp.trans (by
    have HP : a ^ q ≤ a ^ 2 := by
      simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge ha.1 ha1 hq.le
    exact (mul_le_mul_of_nonneg_left HP hh.1.le).trans
      (mul_le_of_le_one_left (sq_nonneg a) (hh.2.trans (min_le_right _ _))))
  have Hweak (i : Fin 2) : 0 ≤ p.2 i.succ ∧ p.2 i.succ ≤ a / 16 := by
    have hZi : 0 ≤ Z i.succ ∧ Z i.succ ≤ 2 * ε * a := by fin_cases i; exact h₂; exact h₃
    constructor
    · exact (div_nonneg hZi.1 (by norm_num)).trans (hw i).1
    · have H := (hw i).2.1.trans (mul_le_mul_of_nonneg_left hZi.2 (by norm_num))
      nlinarith only [H, mul_le_mul_of_nonneg_right hε.2 ha.1.le]
  have hpsmall : ‖p‖ ≤ 8 * a := by
    rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs, abs_of_pos (show 0 < p.1 from hnpos)]
    refine ⟨hnsq.trans ?_, hc⟩
    nlinarith only [ha.1, ha1]
  obtain ⟨hd, Hlo, Hhi⟩ := restartProjectionHeight_shear_bounds
    ⟨ha.1, by linarith only [hasmall]⟩ hσ hshear ⟨hnpos.le, hnsq⟩ (Hweak 0) (Hweak 1)
  have Hgerm := (eventually_restartSectionProjectionHeight_eq hrad hT (by linarith only [hneg])).comp_tendsto
    (hasDerivAt_restartShearCurve σ n₂ n₃ ρ).continuousAt
  change (fun t => restartProjectionHeight (restartSectionRadialState h T (restartShearCurve σ n₂ n₃ t))) =ᶠ[𝓝 ρ]
    restartFastShearHeight h T σ n₂ n₃ at Hgerm
  have HD := restartProjectionHeight_derivative_bound Hcurve hd hpsmall hv
  have Hactual := HD.1.hasDerivAt.congr_of_eventuallyEq Hgerm.symm
  change a ^ 2 / 4 ≤ restartProjectionHeight p at Hlo
  change restartProjectionHeight p ≤ 6 * a ^ 2 at Hhi
  have heq : restartProjectionHeight p = 1 + x 0 := Hgerm.eq_of_nhds
  rw [heq] at Hlo Hhi
  have hA : 0 < 1 + x 0 := (by positivity [ha.1] : 0 < a ^ 2 / 4).trans_le Hlo
  have Hchart := ((contDiffAt_restartSectionChart hrad 1).differentiableAt (by norm_num)).comp ρ
    (hasDerivAt_restartShearCurve σ n₂ n₃ ρ).differentiableAt
  have HX := (hasFDerivAt_normalizedMaxCurve_initial hdom).differentiableAt.comp ρ Hchart
  have HY := ((contDiffAt_toProjectiveState 1 hA.ne').differentiableAt (by norm_num)).comp ρ HX
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := by positivity
  have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := by nlinarith only [hsqrt, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hsqrt2 : Real.sqrt (3 : ℝ) ≤ 2 := by nlinarith only [hsqrt, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have Hcoord (u u₀ : ℝ) (hu₀ : 0 ≤ u₀) (hu : u₀ / 2 ≤ u ∧ u ≤ 2 * u₀) :
      u₀ / (12 * a ^ 2) ≤ Real.sqrt 3 * u / (1 + x 0) ∧
        Real.sqrt 3 * u / (1 + x 0) ≤ 16 * u₀ / a ^ 2 := by
    have hu0 : 0 ≤ u := (div_nonneg hu₀ (by norm_num)).trans hu.1
    constructor
    · calc
        _ = (u₀ / 2) / (6 * a ^ 2) := by ring
        _ ≤ _ := div_le_div₀ (by positivity)
          (hu.1.trans (by nlinarith only [mul_le_mul_of_nonneg_right hsqrt1 hu0])) hA Hhi
    · calc
        _ ≤ (4 * u₀) / (a ^ 2 / 4) := div_le_div₀ (by positivity)
          (by nlinarith only [mul_le_mul_of_nonneg_right hsqrt2 hu0, hu.2]) (by positivity [ha.1]) Hlo
        _ = _ := by ring
  have HV := Hcoord (x 3) n₂ h₂.1 ⟨(hw 0).1, (hw 0).2.1⟩
  have HW := Hcoord (x 4) n₃ h₃.1 ⟨(hw 1).1, (hw 1).2.1⟩
  have hyV : 0 ≤ y 2 := (div_nonneg h₂.1 (by positivity)).trans HV.1
  have hyW : 0 ≤ y 3 := (div_nonneg h₃.1 (by positivity)).trans HW.1
  refine ⟨hdom, HY, Hactual.differentiableAt, Hlo, Hhi, ?_, ?_, ?_, HV, HW, ?_, ?_⟩
  · rw [Hactual.deriv]
    exact HD.2.trans (by ring_nf; rfl)
  · have heqM : σ * y 0 = Real.sqrt 3 * (σ * x 1) / (1 + x 0) := by
      change σ * (Real.sqrt 3 * x 1 / (1 + x 0)) = _
      ring
    rw [heqM]
    have hspos : 0 ≤ σ * x 1 := (by positivity [ha.1] : 0 ≤ 3 * a / 4).trans hshear.1
    constructor
    · calc
        _ = (3 * a / 4) / (6 * a ^ 2) := by field_simp; ring
        _ ≤ _ := div_le_div₀ (by positivity [ha.1])
          (hshear.1.trans (by nlinarith only [mul_le_mul_of_nonneg_right hsqrt1 hspos])) hA Hhi
    · calc
        _ ≤ (2 * (9 * a / 4)) / (a ^ 2 / 4) := div_le_div₀ (by positivity [ha.1])
          (by nlinarith only [mul_le_mul_of_nonneg_right hsqrt2 hspos, hshear.2]) (by positivity [ha.1]) Hlo
        _ = _ := by field_simp; ring
  · refine ⟨div_pos (mul_pos hsqrt hnpos) hA, ?_⟩
    calc
      y 1 ≤ (2 * (h * a ^ q)) / (a ^ 2 / 4) := div_le_div₀ (by positivity [hh.1, ha.1])
        (by
          change Real.sqrt 3 * x 2 ≤ 2 * (h * a ^ q)
          nlinarith only [mul_le_mul_of_nonneg_right hsqrt2 hnpos.le, hnexp]) (by positivity [ha.1]) Hlo
      _ = _ := by rw [Real.rpow_sub ha.1, Real.rpow_two]; ring
  · refine ⟨add_nonneg hyV hyW, ?_⟩
    calc
      y 2 + y 3 ≤ 16 * n₂ / a ^ 2 + 16 * n₃ / a ^ 2 := add_le_add HV.2 HW.2
      _ ≤ 16 * (2 * ε * a) / a ^ 2 + 16 * (2 * ε * a) / a ^ 2 := by gcongr; exact h₂.2; exact h₃.2
      _ = _ := by field_simp; ring
  · refine ⟨mul_nonneg hyV hyW, ?_⟩
    calc
      y 2 * y 3 ≤ (16 * n₂ / a ^ 2) * (16 * n₃ / a ^ 2) :=
        mul_le_mul HV.2 HW.2 hyW (by positivity [h₂.1])
      _ = _ := by ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartShearTail_control :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 2 < q → 0 ≤ D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε ζ ν : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 ≤ ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 ≤ ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let Z := restartShearCurve 1 ζ ν ρ
            let t₀ := q / 2 * Real.log (1 / a)
            let T := shearTailTime a D
            let x := restartSectionChart h Z
            let y := normalizedMaxCurve x 0 t₀
            a ≤ 1 ∧ 0 ≤ t₀ ∧ 0 ≤ T ∧ 0 < restartSectionRadicand h Z ∧ stateConstraint x = 1 ∧
            (∀ t ∈ Icc (0 : ℝ) T,
              let w := restartShearTailFlow h a q ζ ν t ρ
              t + t₀ ∈ normalizedMaxDomain x 0 ∧ w = normalizedMaxCurve y 0 t ∧
              stateConstraint w = 1 ∧ (0 ≤ w 2 ∧ 0 ≤ w 3 ∧ 0 ≤ w 4) ∧
              shearTailRegion a w ∧ w 2 ≤ h * a ^ q * Real.exp (-2 * t) ∧
              w 3 ≤ 2 * ζ * Real.exp (6 * a * t) ∧
              w 4 ≤ 4 * ε * a * Real.exp (-(a / 2) * t) ∧
              |w 1 - y 1| ≤ 48 * ε ^ 2 * a + ζ ^ 2 / a * a ^ (-12 * D) + h * a ^ (q + 1) / 8 ∧
              a ^ 2 / 10 ≤ 1 + w 0 ∧ 1 + w 0 ≤ 6 * a ^ 2 ∧ toProjectiveState w 2 < 1) ∧
            (let w := restartShearTailFlow h a q ζ ν T ρ;
              toProjectiveState w 1 ≤ 20 * h * a ^ (q - 2) ∧
              toProjectiveState w 2 ≤ 40 * ζ * a ^ (-6 * D - 2) ∧
              toProjectiveState w 3 ≤ 80 * ε * a ^ (D / 2 - 1)) := by
  obtain ⟨C, _, hstar, hhstar, HF⟩ := exists_restartShearFastEntry_control
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨aF, haF, HFa⟩ := HF h hh q hq
  obtain ⟨aT, haT, HTa⟩ := exists_shearTail_scale_control hh.1.le hq hD hP
  refine ⟨min aF aT, lt_min haF haT, ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ Z t₀ T x y
  have hε' : 0 ≤ ε ∧ ε ≤ 1 / 64 := ⟨hε.1, by linarith only [hε.2]⟩
  obtain ⟨ha1, _, ht₀, hrad, hdom, hcy, hpy, _, hnpos, hnhi, hsy, _, _, _, HW⟩ :=
    HFa a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε 1 ζ ν hε' (by norm_num)
      ⟨hζ.1, hζ.2.2⟩ hν ρ hρ
  have hcx : stateConstraint x = 1 := restartSectionChart_constraint hrad.le
  have Hn : 0 ≤ y 2 ∧ y 2 ≤ h * a ^ q := ⟨hnpos.le, hnhi⟩
  have Hx : 0 ≤ y 3 ∧ y 3 ≤ 2 * ζ := by
    have H := HW 0
    change ζ / 2 ≤ y 3 ∧ y 3 ≤ 2 * ζ ∧ _ at H
    exact ⟨by linarith only [H.1, hζ.1], H.2.1⟩
  have Hy : 0 ≤ y 4 ∧ y 4 ≤ 4 * ε * a := by
    have H := HW 1
    change ν / 2 ≤ y 4 ∧ y 4 ≤ 2 * ν ∧ _ at H
    exact ⟨by linarith only [H.1, hν.1], by linarith only [H.2.1, hν.2]⟩
  have HS : 3 * a / 4 ≤ y 1 ∧ y 1 ≤ 9 * a / 4 := by
    change 3 * a / 4 ≤ 1 * y 1 ∧ 1 * y 1 ≤ 9 * a / 4 at hsy
    simpa only [one_mul] using hsy
  obtain ⟨hT, HT⟩ := HTa a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε ζ hε
    ⟨hζ.1, hζ.2.1⟩ y hcy (by linarith only [hpy]) HS ⟨Hn.1, Hx.1, Hy.1⟩ ⟨Hn.2, Hx.2, Hy.2⟩
  have Hall (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      t + t₀ ∈ normalizedMaxDomain x 0 ∧
      restartShearTailFlow h a q ζ ν t ρ = normalizedMaxCurve y 0 t ∧
      stateConstraint (restartShearTailFlow h a q ζ ν t ρ) = 1 ∧
      (0 ≤ restartShearTailFlow h a q ζ ν t ρ 2 ∧
        0 ≤ restartShearTailFlow h a q ζ ν t ρ 3 ∧ 0 ≤ restartShearTailFlow h a q ζ ν t ρ 4) := by
    have htime : 0 ≤ t + t₀ := add_nonneg ht.1 ht₀
    have htot := normalizedMaxDomain_contains_Ici_of_constraint hcx 0 htime
    have Heq : restartShearTailFlow h a q ζ ν t ρ = normalizedMaxCurve y 0 t := by
      change normalizedMaxCurve x 0 (t + t₀) = normalizedMaxCurve (normalizedMaxCurve x 0 t₀) 0 t
      simpa only [zero_add] using
        (normalizedMaxCurve_shift (by simpa only [zero_add] using hdom) htot).symm
    refine ⟨htot, Heq, (normalizedMaxCurve_forward_of_constraint hcx htime).2.1, ?_⟩
    rw [Heq]
    exact ⟨(normalizedMaxCurve_wall_sign hcy ht.1 (0 : Fin 3)).2.mpr Hn.1,
      (normalizedMaxCurve_wall_sign hcy ht.1 (1 : Fin 3)).2.mpr Hx.1,
      (normalizedMaxCurve_wall_sign hcy ht.1 (2 : Fin 3)).2.mpr Hy.1⟩
  refine ⟨ha1, ht₀, hT, hrad, hcx, ?_, ?_⟩
  · intro t ht w
    obtain ⟨Hdom, Heq, Hc, Hpos⟩ := Hall t ht
    refine ⟨Hdom, Heq, Hc, Hpos, ?_⟩
    change w = normalizedMaxCurve y 0 t at Heq
    rw [Heq]
    exact (HT t ht).2
  · have heq := (Hall T ⟨hT, le_rfl⟩).2.1
    obtain ⟨_, _, HnT, HxT, HyT, _, HAl, _, _⟩ := HT T ⟨hT, le_rfl⟩
    have Hpos := (Hall T ⟨hT, le_rfl⟩).2.2.2
    rw [heq] at Hpos ⊢
    have Hproj := shearTail_projective_endpoint ⟨ha.1, ha1⟩ hh.1.le hD HAl Hpos ⟨HnT, HxT, HyT⟩
    exact ⟨Hproj.2.1, Hproj.2.2.2.1, Hproj.2.2.2.2.2⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartShearTail_product :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 2 < q → 2 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 128) →
          (0 ≤ ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
          (0 ≤ ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
          let T := shearTailTime a D
          let Y := fun t => restartShearTailProjectiveEntry h a q ζ ν t ρ
          AntitoneOn (fun t => Y t 2 * Y t 3) (Icc 0 T) ∧
          0 ≤ Y T 2 * Y T 3 ∧ Y T 2 * Y T 3 ≤ 256 * ζ * ν / a ^ 4 := by
  obtain ⟨hT, hhT, HT⟩ := exists_restartShearTail_control
  obtain ⟨hF, hhF, HF⟩ := exists_restartFastShearProjectiveEntry_bounds
  refine ⟨min hT hF, lt_min hhT hhF, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨aT, haT, HAT⟩ := HT h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq (by linarith only [hD]) hP
  obtain ⟨aF, haF, HAF⟩ := HF h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q hq
  obtain ⟨aS, haS, HAS⟩ := exists_shearTail_entrance_wall_scale (h := h) hq hD zero_lt_one
  refine ⟨min aT (min aF aS), lt_min haT (lt_min haF haS), ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ T Y
  obtain ⟨_, _, hT0, _, _, Hall, _⟩ :=
    HAT a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, Hfast⟩ :=
    HAF a ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩ ε 1 ζ ν
      ⟨hε.1, by linarith only [hε.2]⟩ (by norm_num) ⟨hζ.1, hζ.2.2⟩ hν ρ hρ
  obtain ⟨_, Hscale⟩ := HAS a
    ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have Hu1 : 20 * h * a ^ (q - 2) ≤ 1 := by
    have hp : 0 ≤ 20 * h * a ^ (q - 2) + 80 * a ^ (D / 2 - 1) := by positivity [hh.1, ha.1]
    have HL := mul_le_mul_of_nonneg_left (show 1 ≤ 1 + |Real.log a| by linarith only [abs_nonneg (Real.log a)]) hp
    have hw0 : 0 ≤ 80 * a ^ (D / 2 - 1) := by positivity [ha.1]
    linarith only [Hscale, HL, hw0]
  let Z := fun t => restartShearTailFlow h a q ζ ν t ρ
  let A := fun t => 1 + Z t 0
  have Hlocal (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivAt Y (A t • projectiveField (Y t)) t ∧ 0 ≤ A t ∧
      (0 ≤ Y t 1 ∧ Y t 1 ≤ 1) ∧ 0 ≤ Y t 2 ∧ 0 ≤ Y t 3 := by
    obtain ⟨hdom, _, hcon, hn, _, Hn, _, _, _, HAl, _, _⟩ := Hall t ht
    have hA : 0 < A t := (by positivity [ha.1] : 0 < a ^ 2 / 10).trans_le HAl
    have HD : HasDerivAt Z (normalizedField (Z t)) t := by
      have H := (hasDerivAt_normalizedMaxCurve hdom).scomp t
        ((hasDerivAt_id t).add_const (q / 2 * Real.log (1 / a)))
      convert! H using 1
      simp only [Z, restartShearTailFlow, one_smul]
    have HY := hasDerivAt_toProjectiveState_normalized HD hA.ne' hcon
    have Hn' : Z t 2 ≤ h * a ^ q := Hn.trans
      (mul_le_of_le_one_right (by positivity [hh.1, ha.1])
        (Real.exp_le_one_iff.mpr (by linarith only [ht.1])))
    obtain ⟨Hu0, Hu⟩ := shearTail_projectiveCoordinate_le ha.1 HAl ⟨hn.1, Hn'⟩
    have Hu' : Y t 1 ≤ 20 * h * a ^ (q - 2) := Hu.trans_eq (by
      rw [Real.rpow_sub ha.1, Real.rpow_two]
      ring)
    have Hv : 0 ≤ Y t 2 := div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hn.2.1) hA.le
    have Hw : 0 ≤ Y t 3 := div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hn.2.2) hA.le
    exact ⟨HY, hA.le, ⟨Hu0, Hu'.trans Hu1⟩, Hv, Hw⟩
  have Hmono := scaled_projective_product_antitone (convex_Icc 0 T)
    (fun t ht => (Hlocal t ht).1) (fun t ht => (Hlocal t ht).2.1)
    (fun t ht => (Hlocal t ht).2.2.1) (fun t ht => (Hlocal t ht).2.2.2.1)
    (fun t ht => (Hlocal t ht).2.2.2.2)
  have Hend := Hlocal T ⟨hT0, le_rfl⟩
  refine ⟨Hmono, mul_nonneg Hend.2.2.2.1 Hend.2.2.2.2, ?_⟩
  have H := Hmono ⟨le_rfl, hT0⟩ ⟨hT0, le_rfl⟩ hT0
  exact H.trans (by simpa only [Y, restartShearTailProjectiveEntry, restartShearTailFlow, zero_add,
    restartFastShearProjectiveEntry] using Hfast.2)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartShearTail_wall_bounds :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 2 < q → 2 < D → 6 * D + 2 < P → ∀ δ > (0 : ℝ),
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 128) →
          (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
          (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
          let y := restartShearTailProjectiveEntry h a q ζ ν (shearTailTime a D) ρ
          a ≤ 1 ∧ y 1 ≤ 20 * h * a ^ (q - 2) ∧
          y 2 ≤ 40 * ζ * a ^ (-6 * D - 2) ∧ y 3 ≤ 80 * a ^ (D / 2 - 1) ∧
          (1 + |Real.log a|) * Real.sqrt (y 1 + y 3) ≤ δ := by
  obtain ⟨hstar, hhstar, HV⟩ := exists_restartShearTail_control
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh q D P hq hD hP δ hδ
  obtain ⟨aV, haV, HAV⟩ := HV h hh q D P hq (by linarith only [hD]) hP
  obtain ⟨aS, haS, HAS⟩ := exists_shearTail_sqrt_wall_scale hh.1.le hq hD hδ
  refine ⟨min aV aS, lt_min haV haS, ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ y
  obtain ⟨_, _, _, _, _, _, Hu, Hv, Hw⟩ :=
    HAV a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε
      ⟨hζ.1.le, hζ.2⟩ ⟨hν.1.le, hν.2⟩ ρ hρ
  change y 1 ≤ 20 * h * a ^ (q - 2) at Hu
  change y 2 ≤ 40 * ζ * a ^ (-6 * D - 2) at Hv
  change y 3 ≤ 80 * ε * a ^ (D / 2 - 1) at Hw
  have Hw' : y 3 ≤ 80 * a ^ (D / 2 - 1) := Hw.trans (by
    have H := mul_le_mul_of_nonneg_right (show ε ≤ 1 by linarith only [hε.2])
      (by positivity [ha.1] : 0 ≤ 80 * a ^ (D / 2 - 1))
    nlinarith only [H])
  obtain ⟨ha1, Hsmall⟩ := HAS a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩
  exact ⟨ha1, Hu, Hv, Hw', (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (add_le_add Hu Hw')) (by positivity)).trans Hsmall⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartShearTail_core_inputs :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
        ∀ η ∈ Ioc (0 : ℝ) (1 / 10000), ∃ astar > (0 : ℝ),
          ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
            (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let Y := restartShearTailProjectiveEntry h a q ζ ν (shearTailTime a D)
            let k := coreRadius (Y ρ 0) (Y ρ 2)
            a ≤ 1 ∧ DifferentiableAt ℝ Y ρ ∧ 8 ≤ k ∧
            1 / (24 * a) ≤ k ∧ k ≤ 64 / a ∧ 1 < Y ρ 0 ∧
            (0 < Y ρ 1 ∧ Y ρ 1 ≤ 1 / 10000) ∧ (0 < Y ρ 2 ∧ Y ρ 2 < 1) ∧
            (0 < Y ρ 3 ∧ Y ρ 3 ≤ 1 / 10000) ∧
            Y ρ 1 + Y ρ 2 * Y ρ 3 ≤ η / (2 * k) ∧
            Y ρ 1 ≤ 20 * h * a ^ (q - 2) ∧ Y ρ 3 ≤ 80 * a ^ (D / 2 - 1) := by
  obtain ⟨hI, hhI, HI⟩ := exists_restartShearTail_entrance_inputs
  obtain ⟨hW, hhW, HW⟩ := exists_restartShearTail_wall_bounds
  refine ⟨min hI hW, lt_min hhI hhW, ?_⟩
  intro h hh q D P hq hD hP η hη
  have hq' : 2 < q := by linarith only [hq]
  have hD' : 2 < D := by linarith only [hD]
  obtain ⟨_, _, HBI⟩ := HI h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D hq' hD'
  obtain ⟨aI, haI, HAI⟩ := HBI P hP (1 / 10000) ⟨by norm_num, le_rfl⟩
  obtain ⟨aW, haW, HAW⟩ := HW h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D P hq' hD' hP 1 zero_lt_one
  obtain ⟨aS, haS, HAS⟩ := exists_shearTail_core_wall_scale hh.1.le hq hD hη.1
  refine ⟨min aI (min aW aS), lt_min haI (lt_min haW haS), ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ Y k
  obtain ⟨HY, hk, hklo, hkhi, hm, hu, hv, hw, _⟩ :=
    HAI a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨ha1, Hu, _, Hw, _⟩ :=
    HAW a ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, Hsmall⟩ := HAS a
    ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  change 8 ≤ k at hk
  change k ≤ 64 / a at hkhi
  have hk0 : 0 < k := by linarith only [hk]
  have Hsum : Y ρ 1 + Y ρ 2 * Y ρ 3 ≤ η * a / 128 :=
    (add_le_add le_rfl (mul_le_of_le_one_left hw.1.le hv.2.le)).trans ((add_le_add Hu Hw).trans Hsmall)
  have Hbudget : Y ρ 1 + Y ρ 2 * Y ρ 3 ≤ η / (2 * k) := Hsum.trans (by
    calc
      _ = η / (2 * (64 / a)) := by field_simp [ha.1.ne']; ring
      _ ≤ _ := div_le_div_of_nonneg_left hη.1.le (by positivity) (by linarith only [hkhi]))
  exact ⟨ha1, HY, hk, hklo, hkhi, hm, hu, hv, hw, Hbudget, Hu, Hw⟩

end
end

/-- The complete long-tail return retains the original weak-wall product and reaches the reflected ascending section. -/
theorem solution :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 128) →
          (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
          (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
          let s := shearTailTime a D + q / 2 * Real.log (1 / a)
          let x := restartSectionChart h (restartShearCurve 1 ζ ν ρ)
          let p := restartShearReturnParameters h s ζ ν ρ
          let G := restartShearReturnState h s ζ ν ρ
          connectionReturnValid p ∧ s < restartShearReturnTime h s ζ ν ρ ∧
          1 / (96 * a) ≤ G 0 ∧ G 0 ≤ 128 / a ∧
          0 < G 1 ∧ 0 < G 2 ∧ G 1 + G 2 ≤ 512 * ζ * ν / a ^ 4 ∧
          coreRadiusEntry G = projectiveReflection (toProjectiveState
            (normalizedMaxCurve x 0 (restartShearReturnTime h s ζ ν ρ))) := by
  obtain ⟨hI, hhI, HI⟩ := exists_restartShearTail_core_inputs
  obtain ⟨hC, hhC, HC⟩ := exists_restartShearTail_connection
  obtain ⟨hP, hhP, HP⟩ := exists_restartShearTail_product
  obtain ⟨hR, hhR, HR⟩ := exists_restartShearTail_entrance_phase
  refine ⟨min hI (min hC (min hP hR)), lt_min hhI (lt_min hhC (lt_min hhP hhR)), ?_⟩
  intro h hh q D P hq hD hPexp
  have hh' := hh.2.trans (min_le_right _ _)
  have hh'' := hh'.trans (min_le_right _ _)
  have hq' : 2 < q := by linarith only [hq]
  have hD' : 2 < D := by linarith only [hD]
  obtain ⟨aI, haI, HAI⟩ := HI h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hPexp
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  obtain ⟨aC, haC, HAC⟩ := HC h ⟨hh.1, hh'.trans (min_le_left _ _)⟩ q D P hq hD hPexp
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  obtain ⟨aP, haP, HAP⟩ := HP h ⟨hh.1, hh''.trans (min_le_left _ _)⟩ q D P hq' hD' hPexp
  obtain ⟨_, _, HBR⟩ := HR h ⟨hh.1, hh''.trans (min_le_right _ _)⟩ q D hq' hD'
  obtain ⟨aR, haR, HAR⟩ := HBR P hPexp
  refine ⟨min aI (min aC (min aP aR)), lt_min haI (lt_min haC (lt_min haP haR)), ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ s x p G
  have ha' := ha.2.trans (min_le_right _ _)
  have ha'' := ha'.trans (min_le_right _ _)
  obtain ⟨_, _, hk, _, _, hm, hu, hv, hw, hsmall, _⟩ :=
    HAI a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨hT, _, hμ, hU, hW, _, hweak, _, hvalid, horbit, _⟩ :=
    HAC a ⟨ha.1, ha'.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, _, Hprod⟩ := HAP a ⟨ha.1, ha''.trans (min_le_left _ _)⟩ ε ζ ν hε
    ⟨hζ.1.le, hζ.2⟩ ⟨hν.1.le, hν.2⟩ ρ hρ
  obtain ⟨_, _, _, _, _, _, _, Hκlo, Hκhi, _⟩ :=
    HAR a ⟨ha.1, ha''.trans (min_le_right _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  let y := restartShearTailProjectiveEntry h a q ζ ν (shearTailTime a D) ρ
  let z := entranceReturnState y
  let κ := coreRadius (z 0) (z 2)
  obtain ⟨_, _, _, _, _, _, hWe, _, _⟩ :=
    entranceReturn_partialCore_entry hk hm.le ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩
      ⟨by norm_num, le_rfl⟩ hsmall
  have Hvalues := entrancePartialCore_reflection_values hk hm.le hu hv hw ⟨by norm_num, le_rfl⟩ hsmall
  change κ / 2 ≤ p 0 ∧ (1 ≤ κ - G 0 ∧ κ - G 0 ≤ 3) ∧ κ / 2 ≤ G 0 ∧ G 0 ≤ κ ∧ _ at Hvalues
  change 1 / (48 * a) ≤ κ at Hκlo
  change κ ≤ 128 / a at Hκhi
  obtain ⟨_, _, Hstrong, Hweak, Hsum, Hentry⟩ := connectionReturn_restart_bounds hμ.1 hU hW
  refine ⟨hvalid, ?_, ?_, Hvalues.2.2.2.1.trans Hκhi, Hstrong.1, Hweak.1, ?_, ?_⟩
  · have htc : 0 < connectionReturnTime p := hvalid.1.1.1
    change s < s + partialCoreDownwardReturnTime y + connectionReturnTime p
    linarith only [hT, htc]
  · calc
      _ = (1 / (48 * a)) / 2 := by ring
      _ ≤ κ / 2 := div_le_div_of_nonneg_right Hκlo (by norm_num)
      _ ≤ _ := Hvalues.2.2.1
  · exact Hsum.trans ((mul_le_mul_of_nonneg_left
      (hweak.trans (hWe.2.trans Hprod)) (by norm_num)).trans_eq (by ring))
  · rw [horbit] at Hentry
    exact Hentry
