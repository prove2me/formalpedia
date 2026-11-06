-- Prove2me | solution 1 for BianchiIX.exists_restartShearTail_radius_comparison
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T05:07:02.986977+00:00
-- url     : https://prove2.me/submissions/e5eb951a-b880-4399-858f-3b1d95b6ada6

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_ShearTransportData
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturn
import Definitions.Def_BianchiIX_Dynamics_EntranceReturn
import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_Dynamics_ConnectionPhysicalReturn
import Definitions.Def_BianchiIX_Dynamics_CoreConnectionChart
import Theorems.Thm_BianchiIX_entrancePartialCore_reflection_values
import Theorems.Thm_BianchiIX_exists_common_rpow_budget
import Theorems.Thm_BianchiIX_exists_restartShearFastEntry_control
import Theorems.Thm_BianchiIX_exists_restartShearTail_connection_curve
import Theorems.Thm_BianchiIX_exists_restartShearTail_core_cone
import Theorems.Thm_BianchiIX_exists_restartShearTail_entrance_inputs
import Theorems.Thm_BianchiIX_exists_restartShearTail_entrance_phase
import Theorems.Thm_BianchiIX_hasDerivAt_normalized_components
import Theorems.Thm_BianchiIX_le_exp_of_clock_deriv_le
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxCurve_shift
import Theorems.Thm_BianchiIX_normalizedMaxCurve_wall_sign
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_shearTail_constraint_bounds
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
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
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
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

private theorem BianchiIX.two_stage_radius_response {k μ dk df dg : ℝ} (hk : 0 < k) (hμ : k / 2 ≤ μ)
    (hdk : dk ≠ 0) (hdf : df ≠ 0) (hf : |df / dk| ≤ 5 / 4)
    (hcore : |df / dk - 1| ≤ 1 / (32 * k))
    (hconn : |dg / df - 1| ≤ 1 / (4 * μ)) :
    |dg - dk| ≤ |dk| / k := by
  have hμ0 : 0 < μ := (half_pos hk).trans_le hμ
  have hcore' : |df - dk| ≤ (1 / (32 * k)) * |dk| := by
    rw [div_sub_one hdk, abs_div] at hcore
    exact (div_le_iff₀ (abs_pos.mpr hdk)).mp hcore
  have hconn' : |dg - df| ≤ (1 / (4 * μ)) * |df| := by
    rw [div_sub_one hdf, abs_div] at hconn
    exact (div_le_iff₀ (abs_pos.mpr hdf)).mp hconn
  have hf' : |df| ≤ (5 / 4) * |dk| := by
    rw [abs_div] at hf
    exact (div_le_iff₀ (abs_pos.mpr hdk)).mp hf
  have hden : 1 / (4 * μ) ≤ 1 / (2 * k) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith only [hμ])
  calc
    _ ≤ |dg - df| + |df - dk| := abs_sub_le dg df dk
    _ ≤ (1 / (4 * μ)) * |df| + (1 / (32 * k)) * |dk| := add_le_add hconn' hcore'
    _ ≤ (1 / (2 * k)) * ((5 / 4) * |dk|) + (1 / (32 * k)) * |dk| := by gcongr
    _ = (21 / 32) * (|dk| / k) := by ring
    _ ≤ _ := mul_le_of_le_one_left (div_nonneg (abs_nonneg _) hk.le) (by norm_num)

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

/-- The core and long connection have bounded radius displacement and an inverse-scale ordinary derivative error. -/
theorem solution :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 128) →
          (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
          (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
          let s := shearTailTime a D + q / 2 * Real.log (1 / a)
          let κ := restartShearTailEntranceRadius h a q D ζ ν
          let g := fun r => restartShearReturnState h s ζ ν r 0
          DifferentiableAt ℝ κ ρ ∧ DifferentiableAt ℝ g ρ ∧
          1 / (96 * a) ≤ κ ρ ∧ 1 / (96 * a) ≤ g ρ ∧
          |g ρ - κ ρ| ≤ 3 ∧ |deriv κ ρ| ≤ 24576 / a ^ 2 ∧
          |deriv g ρ - deriv κ ρ| ≤ 1179648 / a := by
  obtain ⟨hI, hhI, HI⟩ := exists_restartShearTail_core_inputs
  obtain ⟨hR, hhR, HR⟩ := exists_restartShearTail_entrance_phase
  obtain ⟨hC, hhC, HC⟩ := exists_restartShearTail_core_cone
  obtain ⟨hG, hhG, HG⟩ := exists_restartShearTail_connection_curve
  refine ⟨min hI (min hR (min hC hG)), lt_min hhI (lt_min hhR (lt_min hhC hhG)), ?_⟩
  intro h hh q D P hq hD hP
  have hh' := hh.2.trans (min_le_right _ _)
  have hh'' := hh'.trans (min_le_right _ _)
  obtain ⟨aI, haI, HAI⟩ := HI h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  obtain ⟨_, _, HBR⟩ := HR h ⟨hh.1, hh'.trans (min_le_left _ _)⟩ q D
    (by linarith only [hq]) (by linarith only [hD])
  obtain ⟨aR, haR, HAR⟩ := HBR P hP
  obtain ⟨aC, haC, HAC⟩ := HC h ⟨hh.1, hh''.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨aG, haG, HAG⟩ := HG h ⟨hh.1, hh''.trans (min_le_right _ _)⟩ q D P hq hD hP
  refine ⟨min aI (min aR (min aC aG)), lt_min haI (lt_min haR (lt_min haC haG)), ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ s κ g
  have ha' := ha.2.trans (min_le_right _ _)
  have ha'' := ha'.trans (min_le_right _ _)
  obtain ⟨_, _, hk8, _, _, hm, hu, hv, hw, hsmall, _⟩ :=
    HAI a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, _, _, _, _, _, HK, hκlo, _, _, Hκder⟩ :=
    HAR a ⟨ha.1, ha'.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨hκ6, _, _, hκneg, hfneg, Hcore, Hbounds, _⟩ :=
    HAC a ⟨ha.1, ha''.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨HGdiff, _, _, _, _, _, Hconn, _⟩ :=
    HAG a ⟨ha.1, ha''.trans (min_le_right _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  let Y := restartShearTailProjectiveEntry h a q ζ ν (shearTailTime a D)
  let f := fun r => partialCoreDownwardReturnState (Y r) 0
  have HV := entrancePartialCore_reflection_values hk8 hm.le hu hv hw ⟨by norm_num, le_rfl⟩ hsmall
  change κ ρ / 2 ≤ restartShearReturnParameters h s ζ ν ρ 0 ∧
    (1 ≤ κ ρ - g ρ ∧ κ ρ - g ρ ≤ 3) ∧ κ ρ / 2 ≤ g ρ ∧ g ρ ≤ κ ρ ∧ _ at HV
  change 6 ≤ κ ρ at hκ6
  change 1 / (48 * a) ≤ κ ρ at hκlo
  change -deriv κ ρ ≤ 24576 / a ^ 2 at Hκder
  change deriv κ ρ < 0 at hκneg
  change deriv f ρ < 0 at hfneg
  have hκpos : 0 < κ ρ := by linarith only [hκ6]
  have hratio : |deriv f ρ / deriv κ ρ| ≤ 5 / 4 := by
    rw [abs_of_nonneg (div_pos_of_neg_of_neg hfneg hκneg).le]
    exact Hbounds.2
  have Hd := two_stage_radius_response hκpos HV.1 hκneg.ne hfneg.ne hratio Hcore Hconn
  have hκabs : |deriv κ ρ| ≤ 24576 / a ^ 2 := by rwa [abs_of_neg hκneg]
  have Hgκ : |deriv g ρ - deriv κ ρ| ≤ 1179648 / a := Hd.trans (by
    calc
      _ ≤ (24576 / a ^ 2) / (1 / (48 * a)) :=
        div_le_div₀ (by positivity) hκabs (by positivity [ha.1]) hκlo
      _ = _ := by field_simp; ring)
  have Hg : DifferentiableAt ℝ g ρ := differentiableAt_pi.mp (HGdiff.differentiableAt (by norm_num)) 0
  refine ⟨HK, Hg, ?_, ?_, ?_, hκabs, Hgκ⟩
  · exact (div_le_div_of_nonneg_left (by norm_num) (by positivity [ha.1]) (by linarith only [ha.1])).trans hκlo
  · calc
      _ = (1 / (48 * a)) / 2 := by ring
      _ ≤ κ ρ / 2 := div_le_div_of_nonneg_right hκlo (by norm_num)
      _ ≤ _ := HV.2.2.1
  · rw [abs_of_nonpos (sub_nonpos.mpr HV.2.2.2.1)]
    linarith only [HV.2.1.2]
