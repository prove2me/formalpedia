-- Prove2me | solution 1 for BianchiIX.exists_restartShear_common_statistical_preparation
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T05:09:07.701557+00:00
-- url     : https://prove2.me/submissions/c6555a7e-1418-4cb4-943b-456424c160f4

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Analysis_AmplitudeExtension
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Definitions.Def_BianchiIX_ShearTransportData
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturn
import Definitions.Def_BianchiIX_Dynamics_EntranceReturn
import Theorems.Thm_BianchiIX_amplitudeCurveExtension_cone
import Theorems.Thm_BianchiIX_amplitudeCurveExtension_deriv_middle
import Theorems.Thm_BianchiIX_amplitudeCurveExtension_middle
import Theorems.Thm_BianchiIX_amplitudeCurveExtension_pair_bound
import Theorems.Thm_BianchiIX_amplitudeCurveExtension_pos
import Theorems.Thm_BianchiIX_contDiff_amplitudeCurveExtension
import Theorems.Thm_BianchiIX_exists_restartShearReturn_all_active_phase_quarter
import Theorems.Thm_BianchiIX_exists_restartShearReturn_common_bounds
import Theorems.Thm_BianchiIX_exists_restartShearReturn_common_cone
import Theorems.Thm_BianchiIX_exists_restartShearReturn_common_regular
import Theorems.Thm_BianchiIX_exists_restartShearTail_cutoff_germs
import Theorems.Thm_BianchiIX_exists_restartShearTail_entrance_phase
import Theorems.Thm_BianchiIX_exists_restartShearTail_radius_comparison
import Theorems.Thm_BianchiIX_intervalRadiusInverse_control
import Theorems.Thm_BianchiIX_jointly_measurable_amplitudeCurve
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
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.List.Induction
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Floor.Semiring

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX

private theorem BianchiIX.reciprocal_difference_value_bound {α F R : ℝ} (hα : 0 < α)
    (hF : 1 / α ≤ F) (hR : 1 / α ≤ R) :
    |2 / F - 2 / R| ≤ 2 * α ^ 2 * |F - R| := by
  have hF0 : 0 < F := (one_div_pos.mpr hα).trans_le hF
  have hR0 : 0 < R := (one_div_pos.mpr hα).trans_le hR
  have hFi : 1 / F ≤ α := (div_le_iff₀ hF0).mpr (by
    have H := (div_le_iff₀ hα).mp hF; nlinarith only [H])
  have hRi : 1 / R ≤ α := (div_le_iff₀ hR0).mpr (by
    have H := (div_le_iff₀ hα).mp hR; nlinarith only [H])
  have Heq : 2 / F - 2 / R = -2 * (F - R) / (R * F) := by field_simp; ring
  rw [Heq, abs_div, abs_mul, abs_of_pos (mul_pos hR0 hF0)]
  norm_num only [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ = (2 * |F - R|) * (1 / R * (1 / F)) := by ring
    _ ≤ (2 * |F - R|) * (α * α) := by gcongr
    _ = _ := by ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.reciprocal_difference_derivative_bound {α F R Θ p q D : ℝ} (hα : 0 < α)
    (hF : 1 / α ≤ F) (hR : 1 / α ≤ R) (hq : |q| ≤ D / α ^ 2) :
    |-2 * p / F ^ 2 + 2 * Θ * (F + R) * q / (R ^ 2 * F ^ 2)| ≤
      2 * α ^ 2 * |p| + 4 * D * α * |Θ| := by
  have hF0 : 0 < F := (one_div_pos.mpr hα).trans_le hF
  have hR0 : 0 < R := (one_div_pos.mpr hα).trans_le hR
  have hFi : 1 / F ≤ α := (div_le_iff₀ hF0).mpr (by
    have H := (div_le_iff₀ hα).mp hF; nlinarith only [H])
  have hRi : 1 / R ≤ α := (div_le_iff₀ hR0).mpr (by
    have H := (div_le_iff₀ hα).mp hR; nlinarith only [H])
  have hFi2 : 1 / F ^ 2 ≤ α ^ 2 := by
    simpa only [div_pow, one_pow] using pow_le_pow_left₀ (by positivity : 0 ≤ 1 / F) hFi 2
  have HC : (F + R) / (R ^ 2 * F ^ 2) ≤ 2 * α ^ 3 := by
    calc
      _ = (1 / R) * (1 / R) * (1 / F) + (1 / R) * (1 / F) * (1 / F) := by field_simp
      _ ≤ α * α * α + α * α * α := by gcongr
      _ = _ := by ring
  calc
    _ ≤ |-2 * p / F ^ 2| + |2 * Θ * (F + R) * q / (R ^ 2 * F ^ 2)| := abs_add_le _ _
    _ = (2 * |p|) * (1 / F ^ 2) + (2 * |Θ|) * ((F + R) / (R ^ 2 * F ^ 2)) * |q| := by
      rw [abs_div, abs_div]
      simp only [abs_mul, abs_neg, abs_of_pos hF0, abs_of_pos hR0,
        abs_of_pos (add_pos hF0 hR0), abs_pow]
      norm_num
      ring
    _ ≤ (2 * |p|) * α ^ 2 + (2 * |Θ|) * (2 * α ^ 3) * (D / α ^ 2) := by gcongr
    _ = _ := by field_simp; ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartReferenceRoot_sq {n : ℝ} (hn : n ^ 2 ≤ 1) :
    restartReferenceRoot n ^ 2 = 1 - n ^ 2 := Real.sq_sqrt (sub_nonneg.mpr hn)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_reciprocal_error {f k : ℝ → ℝ} {x df dk : ℝ}
    (hf : HasDerivAt f df x) (hk : HasDerivAt k dk x) (hf0 : f x ≠ 0) (hk0 : k x ≠ 0) :
    HasDerivAt (fun y => 2 / f y - 2 / k y)
      (-2 * (df - dk) / (f x) ^ 2 +
        2 * (f x - k x) * (f x + k x) * dk / ((k x) ^ 2 * (f x) ^ 2)) x := by
  have Hf : HasDerivAt (fun y => 2 / f y) (-2 * df / (f x) ^ 2) x := by
    convert! (hasDerivAt_const x (2 : ℝ)).div hf hf0 using 1
    ring
  have Hk : HasDerivAt (fun y => 2 / k y) (-2 * dk / (k x) ^ 2) x := by
    convert! (hasDerivAt_const x (2 : ℝ)).div hk hk0 using 1
    ring
  have H : HasDerivAt (fun y => 2 / f y - 2 / k y)
      (-2 * df / (f x) ^ 2 - (-2 * dk / (k x) ^ 2)) x := Hf.sub Hk
  convert! H using 1
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restart_coefficients_small {n : ℝ} (hn : 0 ≤ n ∧ n ≤ 1 / 16) :
    0 ≤ restartShearFactor n - 1 ∧ restartShearFactor n - 1 ≤ n ∧
      0 ≤ restartWallFactor n - 1 ∧ restartWallFactor n - 1 ≤ n ∧
      0 ≤ restartShearCoupling n ∧ restartShearCoupling n ≤ n := by
  let z := restartReferenceRoot n
  have hz0 : 0 ≤ z := Real.sqrt_nonneg _
  have hz2 : z ^ 2 = 1 - n ^ 2 := restartReferenceRoot_sq (by nlinarith only [hn.1, hn.2])
  have hz1 : z ≤ 1 := by nlinarith only [hz0, hz2, sq_nonneg n]
  have hzhalf : 1 / 2 ≤ z := by nlinarith only [hz0, hz2, hn.1, hn.2]
  have hzsmall : 1 - z ≤ n := by
    nlinarith only [hz2, hn.1, hn.2, mul_nonneg hz0 (sub_nonneg.mpr hz1)]
  have hd : 0 < 2 + z := by positivity
  have hd2 : 0 < 2 * (2 + z) ^ 2 := by positivity
  have ha : restartShearFactor n - 1 = (1 - z) / (2 + z) := by
    dsimp only [restartShearFactor]
    change 3 / (2 + z) - 1 = _
    field_simp
    ring
  have hc : restartWallFactor n - 1 = (1 - z) * (2 * z + 1) / (2 * (2 + z) ^ 2) := by
    dsimp only [restartWallFactor]
    change 9 * (1 + z) / (2 * (2 + z) ^ 2) - 1 = _
    field_simp
    ring
  have ha0 : 0 ≤ restartShearFactor n - 1 := by rw [ha]; positivity
  have ha1 : restartShearFactor n - 1 ≤ n := by
    rw [ha]
    apply le_trans _ hzsmall
    apply (div_le_iff₀ hd).mpr
    nlinarith only [mul_nonneg (sub_nonneg.mpr hz1) (show 0 ≤ 1 + z by positivity)]
  have hc0 : 0 ≤ restartWallFactor n - 1 := by rw [hc]; positivity
  have hc1 : restartWallFactor n - 1 ≤ n := by
    rw [hc]
    apply le_trans _ hzsmall
    apply (div_le_iff₀ hd2).mpr
    exact mul_le_mul_of_nonneg_left (by nlinarith only [hz0, sq_nonneg z]) (sub_nonneg.mpr hz1)
  have hk0 : 0 ≤ restartShearCoupling n := by
    dsimp only [restartShearCoupling]
    exact div_nonneg (mul_nonneg (by positivity) hn.1) (sq_nonneg _)
  have hk1 : restartShearCoupling n ≤ n := by
    dsimp only [restartShearCoupling]
    change 3 * Real.sqrt 3 * n / (2 + z) ^ 2 ≤ n
    apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
    have hsqrt : Real.sqrt 3 ≤ 2 := by
      nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
    have H : 3 * Real.sqrt 3 ≤ (2 + z) ^ 2 := by
      nlinarith only [hsqrt, hzhalf, sq_nonneg (z - 1 / 2)]
    nlinarith only [mul_le_mul_of_nonneg_right H hn.1]
  exact ⟨ha0, ha1, hc0, hc1, hk0, hk1⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.reciprocal_radial_comparison {f k : ℝ → ℝ} {x r L D V E : ℝ}
    (hr : 0 < r) (hL : 0 < L) (hD : 0 ≤ D)
    (hf : DifferentiableAt ℝ f x) (hk : DifferentiableAt ℝ k x)
    (hflo : 1 / (L * r) ≤ f x) (hklo : 1 / (L * r) ≤ k x)
    (hvalue : |f x - k x| ≤ V) (hdk : |deriv k x| ≤ D / r ^ 2)
    (hde : |deriv f x - deriv k x| ≤ E / r) :
    DifferentiableAt ℝ (fun t => 2 / f t - 2 / k t) x ∧
      |2 / f x - 2 / k x| ≤ 2 * L ^ 2 * V * r ^ 2 ∧
      |deriv (fun t => 2 / f t - 2 / k t) x| ≤ (2 * L ^ 2 * E + 4 * D * L ^ 3 * V) * r := by
  have hLr : 0 < L * r := mul_pos hL hr
  have hf0 : 0 < f x := (one_div_pos.mpr hLr).trans_le hflo
  have hk0 : 0 < k x := (one_div_pos.mpr hLr).trans_le hklo
  have HD := hasDerivAt_reciprocal_error hf.hasDerivAt hk.hasDerivAt hf0.ne' hk0.ne'
  have hq : |deriv k x| ≤ (D * L ^ 2) / (L * r) ^ 2 := hdk.trans_eq (by field_simp)
  have HB := reciprocal_difference_derivative_bound hLr hflo hklo hq
    (Θ := f x - k x) (p := deriv f x - deriv k x)
  refine ⟨HD.differentiableAt, ?_, ?_⟩
  · exact (reciprocal_difference_value_bound hLr hflo hklo).trans
      ((mul_le_mul_of_nonneg_left hvalue (by positivity)).trans_eq (by ring))
  · rw [HD.deriv]
    apply HB.trans
    calc
      _ ≤ 2 * (L * r) ^ 2 * (E / r) + 4 * (D * L ^ 2) * (L * r) * V :=
        add_le_add (mul_le_mul_of_nonneg_left hde (by positivity))
          (mul_le_mul_of_nonneg_left hvalue (by positivity))
      _ = _ := by field_simp

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
open Set

private theorem BianchiIX.radiusAmplitude_data {k U : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hk : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 k x) (hd : ∀ x ∈ Icc a b, deriv k x < 0)
    (hU : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 U x) (hpos : ∀ x ∈ Icc a b, 0 < U x)
    (hcone : ∀ x ∈ Icc a b, |deriv U x| ≤ Real.sqrt (U x) * |deriv k x|) :
    let J := Icc (k b) (k a)
    let u := radiusAmplitude k U a b
    let du := radiusAmplitudeSlope k U a b
    (∀ x ∈ Icc a b, u (k x) = U x) ∧ (∀ x ∈ J, 0 < u x) ∧
      (∀ x ∈ J, HasDerivWithinAt u (du x) J x) ∧ ContinuousOn du J ∧
      ∀ x ∈ J, |du x| ≤ Real.sqrt (u x) := by
  intro J u du
  obtain ⟨_, _, hleft, hmaps, _, hder⟩ := intervalRadiusInverse_control hab hk hd
  let g := intervalRadiusInverse k a b
  have hgc : ContinuousOn g J := fun x hx => (hder x hx).continuousWithinAt
  have hdk : ContinuousOn (deriv k) (Icc a b) := fun x hx =>
    ((hk x hx).derivWithin (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).continuousAt.continuousWithinAt
  have hdU : ContinuousOn (deriv U) (Icc a b) := fun x hx =>
    ((hU x hx).derivWithin (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).continuousAt.continuousWithinAt
  refine ⟨?_, (fun x hx => hpos (g x) (hmaps hx)), ?_, ?_, ?_⟩
  · intro x hx
    exact congrArg U (hleft hx)
  · intro x hx
    simpa only [u, du, J, g, radiusAmplitude, radiusAmplitudeSlope, Function.comp_def, div_eq_mul_inv] using!
      (((hU (g x) (hmaps hx)).differentiableAt (by norm_num)).hasDerivAt.comp_hasDerivWithinAt x (hder x hx))
  · exact (hdU.comp hgc hmaps).div (hdk.comp hgc hmaps) (fun x hx => (hd (g x) (hmaps hx)).ne)
  · intro x hx
    change |deriv U (g x) / deriv k (g x)| ≤ Real.sqrt (U (g x))
    rw [abs_div]
    exact (div_le_iff₀ (abs_pos.mpr (hd (g x) (hmaps hx)).ne)).mpr (hcone (g x) (hmaps hx))

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.radiusAmplitudeExtension_pair {k U W : ℝ → ℝ} {a b B : ℝ} (hab : a < b)
    (hk : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 k x) (hd : ∀ x ∈ Icc a b, deriv k x < 0)
    (hU : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 U x) (hW : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 W x)
    (hposU : ∀ x ∈ Icc a b, 0 < U x) (hposW : ∀ x ∈ Icc a b, 0 < W x)
    (hconeU : ∀ x ∈ Icc a b, |deriv U x| ≤ Real.sqrt (U x) * |deriv k x|)
    (hconeW : ∀ x ∈ Icc a b, |deriv W x| ≤ Real.sqrt (W x) * |deriv k x|)
    (hB : ∀ x ∈ Icc a b, U x + W x ≤ B) :
    let u := radiusAmplitudeExtension k U a b
    let w := radiusAmplitudeExtension k W a b
    ContDiff ℝ 1 u ∧ ContDiff ℝ 1 w ∧
      (∀ x ∈ Icc a b, u (k x) = U x ∧ w (k x) = W x ∧
        deriv u (k x) = deriv U x / deriv k x ∧ deriv w (k x) = deriv W x / deriv k x) ∧
      ∀ x : ℝ, 0 < u x ∧ 0 < w x ∧ u x + w x ≤ (25 / 16) * B ∧
        |deriv u x| ≤ Real.sqrt (u x) ∧ |deriv w x| ≤ Real.sqrt (w x) := by
  intro u w
  obtain ⟨hba, himage, hleft, hmaps, _, _⟩ := intervalRadiusInverse_control hab hk hd
  obtain ⟨hmatchU, hpu, hdu, hcu, hconeU'⟩ := radiusAmplitude_data hab hk hd hU hposU hconeU
  obtain ⟨hmatchW, hpw, hdw, hcw, hconeW'⟩ := radiusAmplitude_data hab hk hd hW hposW hconeW
  have hconeU1 (x : ℝ) (hx : x ∈ Icc (k b) (k a)) :
      |radiusAmplitudeSlope k U a b x| ≤ 1 * Real.sqrt (radiusAmplitude k U a b x) := by
    simpa only [one_mul] using hconeU' x hx
  have hconeW1 (x : ℝ) (hx : x ∈ Icc (k b) (k a)) :
      |radiusAmplitudeSlope k W a b x| ≤ 1 * Real.sqrt (radiusAmplitude k W a b x) := by
    simpa only [one_mul] using hconeW' x hx
  have hsum (x : ℝ) (hx : x ∈ Icc (k b) (k a)) :
      radiusAmplitude k U a b x + radiusAmplitude k W a b x ≤ B := hB _ (hmaps hx)
  refine ⟨contDiff_amplitudeCurveExtension hba hpu hdu hcu,
    contDiff_amplitudeCurveExtension hba hpw hdw hcw, ?_, ?_⟩
  · intro x hx
    have hxJ : k x ∈ Icc (k b) (k a) := by rw [← himage]; exact mem_image_of_mem k hx
    refine ⟨(amplitudeCurveExtension_middle hxJ (hpu _ hxJ).le).trans (hmatchU x hx),
      (amplitudeCurveExtension_middle hxJ (hpw _ hxJ).le).trans (hmatchW x hx), ?_, ?_⟩
    · change deriv (amplitudeCurveExtension _ _ _ _) (k x) = _
      rw [amplitudeCurveExtension_deriv_middle hba hpu hdu hxJ]
      change deriv U (intervalRadiusInverse k a b (k x)) / deriv k (intervalRadiusInverse k a b (k x)) = _
      rw [hleft hx]
    · change deriv (amplitudeCurveExtension _ _ _ _) (k x) = _
      rw [amplitudeCurveExtension_deriv_middle hba hpw hdw hxJ]
      change deriv W (intervalRadiusInverse k a b (k x)) / deriv k (intervalRadiusInverse k a b (k x)) = _
      rw [hleft hx]
  · intro x
    refine ⟨amplitudeCurveExtension_pos hba.le hpu hconeU1 le_rfl x,
      amplitudeCurveExtension_pos hba.le hpw hconeW1 le_rfl x,
      amplitudeCurveExtension_pair_bound hba.le hpu hpw hconeU1 hconeW1 le_rfl hsum x, ?_, ?_⟩
    · simpa only [u, radiusAmplitudeExtension, one_mul] using amplitudeCurveExtension_cone hba hpu hdu hconeU1 le_rfl x
    · simpa only [w, radiusAmplitudeExtension, one_mul] using amplitudeCurveExtension_cone hba hpw hdw hconeW1 le_rfl x

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_le_abs_add (a b : ℝ) : phaseNorm a b ≤ |a| + |b| := by
  have hr : 0 ≤ phaseNorm a b := Real.sqrt_nonneg _
  have hs := phaseNorm_sq a b
  nlinarith only [hr, hs, sq_abs a, sq_abs b, abs_nonneg a, abs_nonneg b,
    mul_nonneg (abs_nonneg a) (abs_nonneg b)]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_cauchy (a b c d : ℝ) :
    |a * c + b * d| ≤ phaseNorm a b * phaseNorm c d := by
  have hP : 0 ≤ phaseNorm a b := Real.sqrt_nonneg _
  have hQ : 0 ≤ phaseNorm c d := Real.sqrt_nonneg _
  have hsq : (a * c + b * d) ^ 2 ≤ (phaseNorm a b * phaseNorm c d) ^ 2 := by
    rw [mul_pow, phaseNorm_sq, phaseNorm_sq]
    nlinarith only [sq_nonneg (a * d - b * c)]
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hP hQ)).mp (by simpa using hsq)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_phaseNorm_affine_bounds {a b c d ρ ζ : ℝ}
    (hP : 0 < phaseNorm a b) (hρ : 0 < ρ) (hζ : 0 ≤ ζ)
    (hsmall : 3 * ζ * phaseNorm c d ≤ ρ * phaseNorm a b) :
    ∃ v : ℝ,
      HasDerivAt (fun x : ℝ => phaseNorm (a * x - c * ζ) (b * x - d * ζ)) v ρ ∧
      phaseNorm a b / 2 ≤ v ∧ v ≤ phaseNorm a b := by
  let P := phaseNorm a b
  let Q := phaseNorm c d
  let R := phaseNorm (a * ρ - c * ζ) (b * ρ - d * ζ)
  have hQ : 0 ≤ Q := Real.sqrt_nonneg _
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hC := (abs_le.mp (phaseNorm_cauchy a b c d)).2
  have hC' := (abs_le.mp (phaseNorm_cauchy a b c d)).1
  have hRsq : R ^ 2 = (ρ * P) ^ 2 - 2 * ρ * ζ * (a * c + b * d) + (ζ * Q) ^ 2 := by
    dsimp only [R, P, Q]
    rw [phaseNorm_sq, mul_pow, mul_pow, phaseNorm_sq, phaseNorm_sq]
    ring
  have hPQ : 0 < ρ * P := mul_pos hρ hP
  have hlowpos : 0 < ρ * P - ζ * Q := by
    change 3 * ζ * Q ≤ ρ * P at hsmall
    nlinarith only [hsmall, hPQ, mul_nonneg hζ hQ]
  have hcross := mul_le_mul_of_nonneg_left hC (show 0 ≤ 2 * ρ * ζ by positivity)
  have hcross' := mul_le_mul_of_nonneg_left hC' (show 0 ≤ 2 * ρ * ζ by positivity)
  change _ ≤ 2 * ρ * ζ * (P * Q) at hcross
  change 2 * ρ * ζ * (-(P * Q)) ≤ _ at hcross'
  have hlow : ρ * P - ζ * Q ≤ R := by
    nlinarith only [hRsq, hcross, hlowpos, hR]
  have hupp : R ≤ ρ * P + ζ * Q := by
    nlinarith only [hRsq, hcross', hPQ, mul_nonneg hζ hQ, hR]
  have hRpos : 0 < R := hlowpos.trans_le hlow
  have hnz : (a * ρ - c * ζ) ^ 2 + (b * ρ - d * ζ) ^ 2 ≠ 0 := by
    have H := phaseNorm_sq (a * ρ - c * ζ) (b * ρ - d * ζ)
    change R ^ 2 = _ at H
    nlinarith only [H, sq_pos_of_pos hRpos]
  let v := (a * (a * ρ - c * ζ) + b * (b * ρ - d * ζ)) / R
  have Hv : HasDerivAt (fun x : ℝ => phaseNorm (a * x - c * ζ) (b * x - d * ζ)) v ρ := by
    have Ha := ((hasDerivAt_id ρ).const_mul a).sub_const (c * ζ)
    have Hb := ((hasDerivAt_id ρ).const_mul b).sub_const (d * ζ)
    convert! ((Ha.pow 2).add (Hb.pow 2)).sqrt hnz using 1
    dsimp only [v, R, phaseNorm]
    simp only [Pi.add_apply, Pi.pow_apply, id_eq]
    ring
  have hid : a * (a * ρ - c * ζ) + b * (b * ρ - d * ζ) = ρ * P ^ 2 - ζ * (a * c + b * d) := by
    dsimp only [P]
    rw [phaseNorm_sq]
    ring
  refine ⟨v, Hv, (le_div_iff₀ hRpos).mpr ?_, (div_le_iff₀ hRpos).mpr ?_⟩
  · have H₁ := mul_le_mul_of_nonneg_left hC hζ
    have H₂ := mul_le_mul_of_nonneg_left hupp hP.le
    have H₃ := mul_le_mul_of_nonneg_left hsmall hP.le
    change _ ≤ ζ * (P * Q) at H₁
    rw [hid]
    nlinarith only [H₁, H₂, H₃]
  · exact (abs_le.mp (phaseNorm_cauchy a b (a * ρ - c * ζ) (b * ρ - d * ζ))).2

end
end

section
noncomputable section
open BianchiIX
open Set Function

private theorem BianchiIX.measurableSet_closedIntervalFamily {X : Type*} [MeasurableSpace X]
    {a b : X → ℝ} (ha : Measurable a) (hb : Measurable b) :
    MeasurableSet (closedIntervalFamily a b) :=
  (measurableSet_le (ha.comp measurable_fst) measurable_snd).inter
    (measurableSet_le measurable_snd (hb.comp measurable_fst))

end
end

section
noncomputable section
open BianchiIX
open Set Function

open scoped Classical in

private theorem BianchiIX.jointly_measurable_variable_radiusAmplitude_interior {X : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] {a b : X → ℝ} (ha : Measurable a) (hb : Measurable b)
    (hab : ∀ q, a q < b q) {k U : X → ℝ → ℝ}
    (hk : Measurable (fun p : closedIntervalFamily a b => k p.val.1 p.val.2))
    (hU : Measurable (fun p : closedIntervalFamily a b => U p.val.1 p.val.2))
    (hkc : ∀ q, ContinuousOn (k q) (Icc (a q) (b q)))
    (hanti : ∀ q, StrictAntiOn (k q) (Icc (a q) (b q))) :
    Measurable (fun p : X × ℝ => if k p.1 (b p.1) < p.2 ∧ p.2 < k p.1 (a p.1) then
      radiusAmplitude (k p.1) (U p.1) (a p.1) (b p.1) p.2 else 0) := by
  classical
  let D := closedIntervalFamily a b
  let : StandardBorelSpace D := (measurableSet_closedIntervalFamily ha hb).standardBorel
  let H : D → X × ℝ := fun p => (p.val.1, k p.val.1 p.val.2)
  have hmH : Measurable H := (measurable_fst.comp measurable_subtype_coe).prodMk hk
  have hiH : Injective H := by
    rintro ⟨⟨q, x⟩, hx⟩ ⟨⟨q', y⟩, hy⟩ h
    have hq : q = q' := congrArg Prod.fst h
    subst q'
    have hxy : x = y := (hanti q).injOn hx hy (congrArg Prod.snd h)
    exact Subtype.ext (Prod.ext rfl hxy)
  have he := hmH.measurableEmbedding hiH
  let V := Function.extend H (fun p : D => U p.val.1 p.val.2) (fun _ => (0 : ℝ))
  have hmV : Measurable V := he.measurable_extend hU measurable_const
  have hma' : Measurable (fun q => (⟨(q, a q), le_rfl, (hab q).le⟩ : D)) :=
    (measurable_id.prodMk ha).subtype_mk
  have hmb' : Measurable (fun q => (⟨(q, b q), (hab q).le, le_rfl⟩ : D)) :=
    (measurable_id.prodMk hb).subtype_mk
  have hma : Measurable (fun q => k q (a q)) := hk.comp hma'
  have hmb : Measurable (fun q => k q (b q)) := hk.comp hmb'
  have hS : MeasurableSet {p : X × ℝ | k p.1 (b p.1) < p.2 ∧ p.2 < k p.1 (a p.1)} :=
    (measurableSet_lt (hmb.comp measurable_fst) measurable_snd).inter
      (measurableSet_lt measurable_snd (hma.comp measurable_fst))
  have hmask : Measurable (fun p : X × ℝ =>
      if k p.1 (b p.1) < p.2 ∧ p.2 < k p.1 (a p.1) then V p else 0) :=
    Measurable.ite hS hmV measurable_const
  convert! hmask using 1
  ext p
  by_cases hp : k p.1 (b p.1) < p.2 ∧ p.2 < k p.1 (a p.1)
  · have himage := (hkc p.1).image_Icc_of_antitoneOn (hab p.1).le (hanti p.1).antitoneOn
    obtain ⟨x, hx, hval⟩ : p.2 ∈ k p.1 '' Icc (a p.1) (b p.1) := by
      rw [himage]
      exact ⟨hp.1.le, hp.2.le⟩
    have hinv := (hanti p.1).injOn.leftInvOn_invFunOn hx
    have hV : V p = U p.1 x := by
      have hHp : H (⟨(p.1, x), hx⟩ : D) = p := Prod.ext rfl hval
      rw [← hHp]
      exact hiH.extend_apply _ _ _
    simp [hV, radiusAmplitude, intervalRadiusInverse, ← hval, hinv]
  · simp [hp]

end
end

section
noncomputable section
open BianchiIX
open Set Function

private theorem BianchiIX.jointly_measurable_radiusAmplitude_interior {X : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] {a b : ℝ} (hab : a < b) {k U : X → ℝ → ℝ}
    (hk : Measurable (fun p : X × Icc a b => k p.1 p.2))
    (hU : Measurable (fun p : X × Icc a b => U p.1 p.2))
    (hkc : ∀ q, ContinuousOn (k q) (Icc a b))
    (hanti : ∀ q, StrictAntiOn (k q) (Icc a b)) :
    Measurable (fun p : X × ℝ => if k p.1 b < p.2 ∧ p.2 < k p.1 a then
      radiusAmplitude (k p.1) (U p.1) a b p.2 else 0) := by
  let T : closedIntervalFamily (fun _ : X => a) (fun _ => b) → X × Icc a b :=
    fun p => (p.val.1, ⟨p.val.2, p.property⟩)
  have hT : Measurable T := (measurable_fst.comp measurable_subtype_coe).prodMk
    (measurable_snd.comp measurable_subtype_coe).subtype_mk
  exact jointly_measurable_variable_radiusAmplitude_interior measurable_const measurable_const
    (fun _ => hab) (hk.comp hT) (hU.comp hT) hkc hanti

end
end

section
noncomputable section
open BianchiIX
open Set Function

set_option maxHeartbeats 600000 in

private theorem BianchiIX.jointly_measurable_radiusAmplitudeExtension {X : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] {a b : ℝ} (hab : a < b) {k U : X → ℝ → ℝ}
    (hkm : Measurable (fun p : X × Icc a b => k p.1 p.2))
    (hUm : Measurable (fun p : X × Icc a b => U p.1 p.2))
    (hk : ∀ q x, x ∈ Icc a b → ContDiffAt ℝ 1 (k q) x)
    (hd : ∀ q x, x ∈ Icc a b → deriv (k q) x < 0)
    (hU : ∀ q x, x ∈ Icc a b → ContDiffAt ℝ 1 (U q) x)
    (hpos : ∀ q x, x ∈ Icc a b → 0 < U q x) :
    Measurable (fun p : X × ℝ => radiusAmplitudeExtension (k p.1) (U p.1) a b p.2) ∧
      Measurable (fun p : X × ℝ => deriv (radiusAmplitudeExtension (k p.1) (U p.1) a b) p.2) := by
  have hi (q : X) := intervalRadiusInverse_control hab (hk q) (hd q)
  have hma : Measurable (fun q => k q a) := hkm.comp
    (measurable_id.prodMk (measurable_const (a := (⟨a, le_rfl, hab.le⟩ : Icc a b))))
  have hmb : Measurable (fun q => k q b) := hkm.comp
    (measurable_id.prodMk (measurable_const (a := (⟨b, hab.le, le_rfl⟩ : Icc a b))))
  have hcont (q : X) : ContinuousOn (k q) (Icc a b) :=
    fun x hx => (hk q x hx).continuousAt.continuousWithinAt
  have hanti (q : X) : StrictAntiOn (k q) (Icc a b) :=
    strictAntiOn_of_deriv_neg (convex_Icc a b) (hcont q) (fun x hx => hd q x (interior_subset hx))
  have hm := jointly_measurable_radiusAmplitude_interior hab hkm hUm hcont hanti
  have hrootpos (q : X) (x : ℝ) (hx : x ∈ Icc (k q b) (k q a)) :
      0 < radiusAmplitude (k q) (U q) a b x := hpos q _ ((hi q).2.2.2.1 hx)
  have hrootder (q : X) (x : ℝ) (hx : x ∈ Icc (k q b) (k q a)) :
      HasDerivWithinAt (radiusAmplitude (k q) (U q) a b)
        (radiusAmplitudeSlope (k q) (U q) a b x) (Icc (k q b) (k q a)) x := by
    have H := ((hU q _ ((hi q).2.2.2.1 hx)).differentiableAt (by norm_num)).hasDerivAt.comp_hasDerivWithinAt x
      ((hi q).2.2.2.2.2 x hx)
    simpa only [radiusAmplitude, radiusAmplitudeSlope, Function.comp_def, div_eq_mul_inv] using! H
  exact jointly_measurable_amplitudeCurve
    (U := fun q => radiusAmplitude (k q) (U q) a b)
    (dU := fun q => radiusAmplitudeSlope (k q) (U q) a b)
    hmb hma (fun q => (hi q).1) hrootpos hm hrootder

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartShearCurve_annulus {a ρ σ ε n₂ n₃ : ℝ} (ha : 0 < a)
    (hρ : ρ ∈ Icc a (2 * a)) (hσ : |σ| = 1) (hε : 0 ≤ ε ∧ ε ≤ 1 / 64)
    (h₂ : 0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) (h₃ : 0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) :
    ‖restartShearCurve σ n₂ n₃ ρ‖ ≤ 2 * a ∧
      a ≤ restartRadialNorm (restartShearCurve σ n₂ n₃ ρ) ∧ |n₂ - n₃| ≤ 2 * ε * a := by
  have hρpos := ha.trans_le hρ.1
  have hsmall : 2 * ε * a ≤ 2 * a := by nlinarith only [hε.2, ha]
  refine ⟨?_, ?_, abs_le.mpr ⟨by linarith only [h₂.1, h₃.2], by linarith only [h₃.1, h₂.2]⟩⟩
  · apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * a)).mpr
    intro i
    fin_cases i
    · change |σ * ρ| ≤ 2 * a
      simpa only [abs_mul, hσ, abs_of_pos hρpos, one_mul] using hρ.2
    · exact (show |n₂| ≤ 2 * ε * a by simpa only [abs_of_nonneg h₂.1] using h₂.2).trans hsmall
    · exact (show |n₃| ≤ 2 * ε * a by simpa only [abs_of_nonneg h₃.1] using h₃.2).trans hsmall
  · have H := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg (n₂ - n₃)) :
        (σ * ρ) ^ 2 ≤ (σ * ρ) ^ 2 + (n₂ - n₃) ^ 2)
    rw [Real.sqrt_sq_eq_abs, abs_mul, hσ, abs_of_pos hρpos, one_mul] at H
    exact hρ.1.trans H

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartReferenceRadialPhase_shear_derivative {h σ n₂ n₃ ρ a ε : ℝ}
    (hh : 0 ≤ h ∧ h ≤ 1 / 16) (ha : 0 < a) (hρ : ρ ∈ Icc a (2 * a))
    (hσ : |σ| = 1) (hε : 0 ≤ ε ∧ ε ≤ 1 / 64)
    (h₂ : 0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) (h₃ : 0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) :
    DifferentiableAt ℝ (fun x => restartReferenceRadialPhase h (restartShearCurve σ n₂ n₃ x)) ρ ∧
      1 / (2 * Real.sqrt 3) ≤ deriv (fun x => restartReferenceRadialPhase h (restartShearCurve σ n₂ n₃ x)) ρ ∧
      deriv (fun x => restartReferenceRadialPhase h (restartShearCurve σ n₂ n₃ x)) ρ ≤ 2 / Real.sqrt 3 := by
  obtain ⟨ha0, ha1, hc0, hc1, hk0, hk1⟩ := restart_coefficients_small hh
  let A := restartShearFactor h
  let C := restartWallFactor h
  let K := restartShearCoupling h
  let d := n₂ - n₃
  have hA : 1 ≤ A ∧ A ≤ 2 := by dsimp only [A]; constructor <;> linarith only [ha0, ha1, hh.2]
  have hC : 0 ≤ C ∧ C ≤ 2 := by dsimp only [C]; constructor <;> linarith only [hc0, hc1, hh.2]
  have hK : 0 ≤ K ∧ K ≤ 1 := ⟨hk0, hk1.trans (by linarith only [hh.2])⟩
  have hP : phaseNorm (A * σ) 0 = A := by
    simp only [phaseNorm, zero_pow (by decide : 2 ≠ 0), add_zero, Real.sqrt_sq_eq_abs,
      abs_mul, abs_of_nonneg (by linarith only [hA.1] : 0 ≤ A), hσ, mul_one]
  have hQ : phaseNorm (-(K * d)) (-(C * d)) ≤ 3 * |d| := by
    have H := phaseNorm_le_abs_add (-(K * d)) (-(C * d))
    simp only [abs_neg, abs_mul, abs_of_nonneg hK.1, abs_of_nonneg hC.1] at H
    nlinarith only [H, mul_le_mul_of_nonneg_right hK.2 (abs_nonneg d),
      mul_le_mul_of_nonneg_right hC.2 (abs_nonneg d)]
  have hd : |d| ≤ 2 * ε * a := (restartShearCurve_annulus ha hρ hσ hε h₂ h₃).2.2
  have hsmall : 3 * (1 : ℝ) * phaseNorm (-(K * d)) (-(C * d)) ≤ ρ * phaseNorm (A * σ) 0 := by
    rw [hP]
    have HE := mul_le_mul_of_nonneg_right hε.2 ha.le
    have HP := mul_le_mul_of_nonneg_left hA.1 (ha.trans_le hρ.1).le
    nlinarith only [hQ, hd, HE, HP, hρ.1, ha]
  obtain ⟨v, Hv, hvlo, hvhi⟩ := hasDerivAt_phaseNorm_affine_bounds
    (by rw [hP]; linarith only [hA.1]) (ha.trans_le hρ.1) (by norm_num : (0 : ℝ) ≤ 1) hsmall
  have Href : HasDerivAt (fun x => restartReferenceRadialPhase h (restartShearCurve σ n₂ n₃ x))
      (v / Real.sqrt 3) ρ := by
    convert! Hv.div_const (Real.sqrt 3) using 1
    ext x
    change Real.sqrt (restartQuadratic h (σ * x) (n₂ - n₃)) / Real.sqrt 3 = _
    dsimp only [restartQuadratic, phaseNorm, A, C, K, d]
    congr 2
    ring
  rw [hP] at hvlo hvhi
  refine ⟨Href.differentiableAt, ?_, ?_⟩ <;> rw [Href.deriv]
  · have H : (1 : ℝ) / 2 ≤ v := by linarith only [hA.1, hvlo]
    calc
      _ = (1 / 2) / Real.sqrt 3 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right H (Real.sqrt_nonneg _)
  · exact div_le_div_of_nonneg_right (hvhi.trans hA.2) (Real.sqrt_nonneg _)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartShearTail_output_phase :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D : ℝ, 3 < q → 4 < D → ∃ C > (0 : ℝ),
        ∀ P : ℝ, 6 * D + 2 < P → ∃ astar > (0 : ℝ),
          ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
            (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let s := shearTailTime a D + q / 2 * Real.log (1 / a)
            let X := restartShearReturnPhase h s ζ ν
            let F := fun r => restartReferenceRadialPhase h (restartShearCurve 1 ζ ν r)
            DifferentiableAt ℝ X ρ ∧ |X ρ - F ρ| ≤ C * a ^ 2 ∧
            |deriv X ρ - deriv F ρ| ≤ C * a ∧
            1 / (8 * Real.sqrt 3) ≤ deriv X ρ ∧ deriv X ρ ≤ C := by
  obtain ⟨hR, hhR, HR⟩ := exists_restartShearTail_radius_comparison
  obtain ⟨hE, hhE, HE⟩ := exists_restartShearTail_entrance_phase
  refine ⟨min hR hE, lt_min hhR hhE, ?_⟩
  intro h hh q D hq hD
  obtain ⟨K, hK, HK⟩ := HE h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D
    (by linarith only [hq]) (by linarith only [hD])
  let A : ℝ := 2 * 96 ^ 2 * 1179648 + 4 * 24576 * 96 ^ 3 * 3
  let C := A + K + 2 / Real.sqrt 3 + 2
  have hA : 0 < A := by dsimp only [A]; norm_num
  have hC : 0 < C := by dsimp only [C]; positivity
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := by positivity
  have hAC : A + K ≤ C := by
    have H : 0 < 2 / Real.sqrt (3 : ℝ) := by positivity
    dsimp only [C]
    linarith only [H]
  refine ⟨C, hC, ?_⟩
  intro P hP
  obtain ⟨aR, haR, HAR⟩ := HR h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨aE, haE, HAE⟩ := HK P hP
  refine ⟨min aR (min aE (min (1 / (8 * Real.sqrt 3 * A)) (1 / A))),
    lt_min haR (lt_min haE (lt_min (by positivity) (by positivity))), ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ s X F
  have ha' := ha.2.trans (min_le_right _ _)
  have ha'' := ha'.trans (min_le_right _ _)
  let κ := restartShearTailEntranceRadius h a q D ζ ν
  let g := fun r => restartShearReturnState h s ζ ν r 0
  let f := restartShearTailEntrancePhase h a q D ζ ν
  obtain ⟨Hκ, Hg, hκlo, hglo, Hval, Hκd, Hder⟩ :=
    HAR a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, Hf, Hfv, Hfd, Hflo, Hfhi, _⟩ :=
    HAE a ⟨ha.1, ha'.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  have hg0 : 0 < g ρ := (by positivity [ha.1] : 0 < 1 / (96 * a)).trans_le hglo
  have HX : DifferentiableAt ℝ X ρ :=
    ((hasDerivAt_const ρ (2 : ℝ)).div Hg.hasDerivAt hg0.ne').differentiableAt
  obtain ⟨_, HV, HD⟩ := reciprocal_radial_comparison ha.1 (by norm_num : (0 : ℝ) < 96)
    (by norm_num : (0 : ℝ) ≤ 24576) Hg Hκ hglo hκlo Hval Hκd Hder
  change |X ρ - f ρ| ≤ 2 * 96 ^ 2 * 3 * a ^ 2 at HV
  change |deriv (fun r => X r - f r) ρ| ≤ A * a at HD
  rw [deriv_fun_sub HX Hf] at HD
  have HV' : |X ρ - f ρ| ≤ A * a ^ 2 := HV.trans
    (mul_le_mul_of_nonneg_right (by dsimp only [A]; norm_num) (sq_nonneg a))
  have HA : A * a ≤ 1 / (8 * Real.sqrt 3) := by
    have H := mul_le_mul_of_nonneg_left (ha''.trans (min_le_left _ _)) hA.le
    exact H.trans_eq (by field_simp)
  have HA1 : A * a ≤ 1 := by
    nlinarith only [(le_div_iff₀ hA).mp (ha''.trans (min_le_right _ _))]
  have Habs := abs_le.mp HD
  refine ⟨HX, ?_, ?_, ?_, ?_⟩
  · calc
      _ ≤ |X ρ - f ρ| + |f ρ - F ρ| := abs_sub_le _ _ _
      _ ≤ A * a ^ 2 + K * a ^ 2 := add_le_add HV' Hfv
      _ = (A + K) * a ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hAC (sq_nonneg a)
  · calc
      _ ≤ |deriv X ρ - deriv f ρ| + |deriv f ρ - deriv F ρ| := abs_sub_le _ _ _
      _ ≤ A * a + K * a := add_le_add HD Hfd
      _ = (A + K) * a := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hAC ha.1.le
  · have heq : 1 / (4 * Real.sqrt 3) = 2 * (1 / (8 * Real.sqrt 3)) := by ring
    rw [heq] at Hflo
    linarith only [Hflo, Habs.1, HA]
  · dsimp only [C]
    linarith only [Hfhi, Habs.2, HA1, hA, hK]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_restartShearTail_fast_output_phase :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D : ℝ, 3 < q → 4 < D → ∃ C > (0 : ℝ),
        ∀ P : ℝ, 6 * D + 2 < P → ∃ astar > (0 : ℝ),
          ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
            (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            let X := restartShearReturnPhase h s ζ ν
            let F := fun r => restartReferenceRadialPhase h (restartShearCurve 1 ζ ν r)
            DifferentiableAt ℝ X ρ ∧ |X ρ - F ρ| ≤ C * a ^ 2 ∧
            |deriv X ρ - deriv F ρ| ≤ C * a ∧
            1 / (8 * Real.sqrt 3) ≤ deriv X ρ ∧ deriv X ρ ≤ C := by
  obtain ⟨hG, hhG, HG⟩ := exists_restartShearTail_cutoff_germs
  obtain ⟨hX, hhX, HX⟩ := exists_restartShearTail_output_phase
  refine ⟨min hG hX, lt_min hhG hhX, ?_⟩
  intro h hh q D hq hD
  obtain ⟨C, hC, HC⟩ := HX h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D hq hD
  refine ⟨C, hC, ?_⟩
  intro P hP
  obtain ⟨aG, haG, HAG⟩ := HG h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨aX, haX, HAX⟩ := HC P hP
  refine ⟨min aG aX, lt_min haG haX, ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ s X F
  have H := (HAG a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ).2.2.1
  have hi : ContinuousAt (fun r : ℝ => ((ζ, ν), r)) ρ := continuousAt_const.prodMk continuousAt_id
  have Heq : X =ᶠ[𝓝 ρ] restartShearReturnPhase h (shearTailTime a D + s) ζ ν := hi.tendsto.eventually H
  obtain ⟨hd, hv, hder, hlo, hhi⟩ :=
    HAX a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  refine ⟨hd.congr_of_eventuallyEq Heq, ?_, ?_, ?_, ?_⟩
  · rw [Heq.self_of_nhds]
    exact hv
  · rw [Heq.deriv_eq]
    exact hder
  · rw [Heq.deriv_eq]
    exact hlo
  · rw [Heq.deriv_eq]
    exact hhi

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartShearPhase_deriv_lower {h σ n₂ n₃ ρ a ε C : ℝ} {X : ℝ → ℝ}
    (hh : 0 ≤ h ∧ h ≤ 1 / 16) (ha : 0 < a) (hρ : ρ ∈ Icc a (2 * a))
    (hσ : |σ| = 1) (hε : 0 ≤ ε ∧ ε ≤ 1 / 64)
    (h₂ : 0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) (h₃ : 0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a)
    (herr : |deriv X ρ - deriv (fun r => restartReferenceRadialPhase h (restartShearCurve σ n₂ n₃ r)) ρ| ≤ C * a)
    (hsmall : C * a ≤ 1 / (4 * Real.sqrt 3)) :
    1 / (4 * Real.sqrt 3) ≤ deriv X ρ := by
  have H := (restartReferenceRadialPhase_shear_derivative hh ha hρ hσ hε h₂ h₃).2.1
  have heq : 1 / (2 * Real.sqrt 3) = 2 * (1 / (4 * Real.sqrt 3)) := by ring
  rw [heq] at H
  linarith only [H, (abs_le.mp herr).1, hsmall]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartShearTail_fast_output_phase_quarter :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D : ℝ, 3 < q → 4 < D → ∃ C > (0 : ℝ),
        ∀ P : ℝ, 6 * D + 2 < P → ∃ astar > (0 : ℝ),
          ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
            (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            let X := restartShearReturnPhase h s ζ ν
            let F := fun r => restartReferenceRadialPhase h (restartShearCurve 1 ζ ν r)
            DifferentiableAt ℝ X ρ ∧ |X ρ - F ρ| ≤ C * a ^ 2 ∧
            |deriv X ρ - deriv F ρ| ≤ C * a ∧
            1 / (4 * Real.sqrt 3) ≤ deriv X ρ ∧ deriv X ρ ≤ C := by
  obtain ⟨h₀, hh₀, HH⟩ := exists_restartShearTail_fast_output_phase
  refine ⟨min h₀ (1 / 16), lt_min hh₀ (by norm_num), ?_⟩
  intro h hh q D hq hD
  obtain ⟨C, hC, HC⟩ := HH h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D hq hD
  refine ⟨C, hC, ?_⟩
  intro P hP
  obtain ⟨a₀, ha₀, HA⟩ := HC P hP
  refine ⟨min a₀ (1 / (4 * Real.sqrt 3 * C)), lt_min ha₀ (by positivity), ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ s X F
  obtain ⟨hX, hv, hd, _, hu⟩ := HA a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  refine ⟨hX, hv, hd, ?_, hu⟩
  apply restartShearPhase_deriv_lower ⟨hh.1.le, hh.2.trans (min_le_right _ _)⟩
    ha.1 hρ (by norm_num : |(1 : ℝ)| = 1) ⟨hε.1, by linarith only [hε.2]⟩
    ⟨hζ.1.le, hζ.2.2⟩ ⟨hν.1.le, hν.2⟩ hd
  have H := mul_le_mul_of_nonneg_left (ha.2.trans (min_le_right _ _)) hC.le
  exact H.trans_eq (by field_simp)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartShearReturn_common_phase :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D : ℝ, 3 < q → 4 < D → ∃ C > (0 : ℝ),
        ∀ P : ℝ, 6 * D + 2 < P → ∃ astar > (0 : ℝ),
          ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε n₂ n₃ : ℝ,
            (0 ≤ ε ∧ ε ≤ 1 / 128) → (0 < n₂ ∧ n₂ ≤ 2 * ε * a) →
            (0 < n₃ ∧ n₃ ≤ 2 * ε * a) → min n₂ n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            let X := restartShearReturnPhase h s n₂ n₃
            let F := fun r => restartReferenceRadialPhase h (restartShearCurve 1 n₂ n₃ r)
            DifferentiableAt ℝ X ρ ∧ |X ρ - F ρ| ≤ C * a ^ 2 ∧
            |deriv X ρ - deriv F ρ| ≤ C * a ∧
            1 / (4 * Real.sqrt 3) ≤ deriv X ρ ∧ deriv X ρ ≤ C := by
  obtain ⟨hA, hhA, HA⟩ := exists_restartShearReturn_all_active_phase_quarter
  obtain ⟨hT, hhT, HT⟩ := exists_restartShearTail_fast_output_phase_quarter
  refine ⟨min hA hT, lt_min hhA hhT, ?_⟩
  intro h hh q D hq hD
  obtain ⟨CA, hCA, HCA⟩ := HA h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩
  obtain ⟨CT, hCT, HCT⟩ := HT h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D hq hD
  refine ⟨max CA CT, hCA.trans_le (le_max_left _ _), ?_⟩
  intro P hP
  obtain ⟨aA, haA, HAA⟩ := HCA q P hq (by linarith only [hD, hP])
  obtain ⟨aT, haT, HAT⟩ := HCT P hP
  refine ⟨min aA aT, lt_min haA haT, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ hmin ρ hρ s X F
  by_cases hn₃ : n₃ ≤ a ^ P
  · obtain ⟨hd, hv, he, hlo, hhi⟩ := HAA a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃
      ⟨hε.1, hε.2.trans (by norm_num)⟩ h₂ h₃ hn₃ ρ hρ
    exact ⟨hd, hv.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg a)),
      he.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ha.1.le), hlo, hhi.trans (le_max_left _ _)⟩
  · obtain ⟨hd, hv, he, hlo, hhi⟩ := HAT a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε n₂ n₃ hε
      ⟨h₂.1, (min_le_iff.mp hmin).resolve_right hn₃, h₂.2⟩ h₃ ρ hρ
    exact ⟨hd, hv.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg a)),
      he.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) ha.1.le), hlo, hhi.trans (le_max_right _ _)⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartShearReturn_common_extension :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε n₂ n₃ : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 128) → (0 < n₂ ∧ n₂ ≤ 2 * ε * a) →
          (0 < n₃ ∧ n₃ ≤ 2 * ε * a) → min n₂ n₃ ≤ a ^ P →
          let s := q / 2 * Real.log (1 / a)
          let G := restartShearReturnState h s n₂ n₃
          let u := restartShearAmplitudeExtension h s n₂ n₃ a 1
          let w := restartShearAmplitudeExtension h s n₂ n₃ a 2
          ContDiff ℝ 1 u ∧ ContDiff ℝ 1 w ∧
          (∀ ρ ∈ Icc a (2 * a), u (G ρ 0) = G ρ 1 ∧ w (G ρ 0) = G ρ 2 ∧
            deriv u (G ρ 0) = deriv (fun r => G r 1) ρ / deriv (fun r => G r 0) ρ ∧
            deriv w (G ρ 0) = deriv (fun r => G r 2) ρ / deriv (fun r => G r 0) ρ) ∧
          ∀ k : ℝ, 0 < u k ∧ 0 < w k ∧ u k + w k ≤ 800 * n₂ * n₃ / a ^ 4 ∧
            |deriv u k| ≤ Real.sqrt (u k) ∧ |deriv w k| ≤ Real.sqrt (w k) := by
  obtain ⟨hA, hhA, HA⟩ := exists_restartShearReturn_common_bounds
  obtain ⟨hC, hhC, HC⟩ := exists_restartShearReturn_common_cone
  refine ⟨min hA hC, lt_min hhA hhC, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨aA, haA, HAA⟩ := HA h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨aC, haC, HAC⟩ := HC h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D P hq hD hP
  refine ⟨min aA aC, lt_min haA haC, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ hmin s G u w
  have HA' (ρ : ℝ) (hρ : ρ ∈ Icc a (2 * a)) :
      0 < G ρ 1 ∧ 0 < G ρ 2 ∧ G ρ 1 + G ρ 2 ≤ 512 * n₂ * n₃ / a ^ 4 := by
    obtain ⟨_, _, _, _, _, _, _, hu, hw, hsum, _⟩ :=
      HAA a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ hmin ρ hρ
    exact ⟨hu, hw, hsum⟩
  have HC' (ρ : ℝ) (hρ : ρ ∈ Icc a (2 * a)) :=
    HAC a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε n₂ n₃ hε h₂ h₃ hmin ρ hρ
  have hG (ρ : ℝ) (hρ : ρ ∈ Icc a (2 * a)) (i : Fin 3) :
      ContDiffAt ℝ 1 (fun r => G r i) ρ := (contDiffAt_pi.mp (HC' ρ hρ).1 i).of_le (by norm_num)
  obtain ⟨hcu, hcw, hmatch, hbound⟩ := radiusAmplitudeExtension_pair (by linarith only [ha.1] : a < 2 * a)
    (fun ρ hρ => hG ρ hρ 0) (fun ρ hρ => (HC' ρ hρ).2.1)
    (fun ρ hρ => hG ρ hρ 1) (fun ρ hρ => hG ρ hρ 2)
    (fun ρ hρ => (HA' ρ hρ).1) (fun ρ hρ => (HA' ρ hρ).2.1)
    (fun ρ hρ => (HC' ρ hρ).2.2 0) (fun ρ hρ => (HC' ρ hρ).2.2 1)
    (fun ρ hρ => (HA' ρ hρ).2.2)
  refine ⟨hcu, hcw, hmatch, ?_⟩
  intro k
  obtain ⟨hu, hw, hsum, hdu, hdw⟩ := hbound k
  exact ⟨hu, hw, hsum.trans_eq (by ring), hdu, hdw⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.measurableSet_restartShearCommonLabelSet (ε a P : ℝ) :
    MeasurableSet (restartShearCommonLabelSet ε a P) :=
  ((measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_le measurable_fst measurable_const)).inter
    (((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)).inter
      (measurableSet_le (measurable_fst.min measurable_snd) measurable_const))

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartShearReturn_common_extension_measurable :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 128) →
          let s := q / 2 * Real.log (1 / a)
          Measurable (fun p : restartShearCommonLabelSet ε a P × Icc a (2 * a) =>
            restartShearReturnState h s p.1.val.1 p.1.val.2 p.2) ∧
          ∀ i : Fin 3, (i = 1 ∨ i = 2) →
            Measurable (fun p : restartShearCommonLabelSet ε a P × ℝ =>
              restartShearAmplitudeExtension h s p.1.val.1 p.1.val.2 a i p.2) ∧
            Measurable (fun p : restartShearCommonLabelSet ε a P × ℝ =>
              deriv (restartShearAmplitudeExtension h s p.1.val.1 p.1.val.2 a i) p.2) := by
  obtain ⟨hR, hhR, HR⟩ := exists_restartShearReturn_common_regular
  obtain ⟨hC, hhC, HC⟩ := exists_restartShearReturn_common_cone
  obtain ⟨hA, hhA, HA⟩ := exists_restartShearReturn_common_bounds
  refine ⟨min hR (min hC hA), lt_min hhR (lt_min hhC hhA), ?_⟩
  intro h hh q D P hq hD hP
  have hh' := hh.2.trans (min_le_right _ _)
  obtain ⟨aR, haR, HAR⟩ := HR h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨aC, haC, HAC⟩ := HC h ⟨hh.1, hh'.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨aA, haA, HAA⟩ := HA h ⟨hh.1, hh'.trans (min_le_right _ _)⟩ q D P hq hD hP
  refine ⟨min aR (min aC aA), lt_min haR (lt_min haC haA), ?_⟩
  intro a ha ε hε s
  have ha' := ha.2.trans (min_le_right _ _)
  let X := ↥(restartShearCommonLabelSet ε a P)
  let : StandardBorelSpace X := (measurableSet_restartShearCommonLabelSet ε a P).standardBorel
  let G : X → ℝ → CoreAngleState := fun z r => restartShearReturnState h s z.val.1 z.val.2 r
  have hmap : Continuous (fun p : X × Icc a (2 * a) => (p.1.val, (p.2 : ℝ))) := by
    dsimp only [X]
    fun_prop
  have hGc : Continuous (fun p : X × Icc a (2 * a) => G p.1 p.2) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hstate := (HAR a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε p.1.val.1 p.1.val.2
      hε p.1.property.1 p.1.property.2.1 p.1.property.2.2 p.2 p.2.property).2.1
    exact hstate.continuousAt.comp
      (f := fun p : X × Icc a (2 * a) => (p.1.val, (p.2 : ℝ))) (x := p) hmap.continuousAt
  have hGm (i : Fin 3) : Measurable (fun p : X × Icc a (2 * a) => G p.1 p.2 i) :=
    ((continuous_apply i).comp hGc).measurable
  have H (z : X) (r : ℝ) (hr : r ∈ Icc a (2 * a)) :=
    HAC a ⟨ha.1, ha'.trans (min_le_left _ _)⟩ ε z.val.1 z.val.2 hε
      z.property.1 z.property.2.1 z.property.2.2 r hr
  have Hpos (z : X) (r : ℝ) (hr : r ∈ Icc a (2 * a)) : 0 < G z r 1 ∧ 0 < G z r 2 := by
    obtain ⟨_, _, _, _, _, _, _, hu, hw, _⟩ := HAA a ⟨ha.1, ha'.trans (min_le_right _ _)⟩
      ε z.val.1 z.val.2 hε z.property.1 z.property.2.1 z.property.2.2 r hr
    exact ⟨hu, hw⟩
  have hGtwo (z : X) (r : ℝ) (hr : r ∈ Icc a (2 * a)) (i : Fin 3) :
      ContDiffAt ℝ 2 (fun t => G z t i) r := contDiffAt_pi.mp (H z r hr).1 i
  refine ⟨hGc.measurable, ?_⟩
  intro i hi
  have hpos (z : X) (r : ℝ) (hr : r ∈ Icc a (2 * a)) : 0 < G z r i := by
    rcases hi with rfl | rfl
    · exact (Hpos z r hr).1
    · exact (Hpos z r hr).2
  exact jointly_measurable_radiusAmplitudeExtension (by linarith only [ha.1] : a < 2 * a)
    (hGm 0) (hGm i) (fun z r hr => (hGtwo z r hr 0).of_le (by norm_num))
    (fun z r hr => (H z r hr).2.1)
    (fun z r hr => (hGtwo z r hr i).of_le (by norm_num)) hpos

end
end

private theorem BianchiIX.restartShearAmplitudeBudget_le_of_min {a n₂ n₃ P : ℝ}
    (ha : 0 < a ∧ a ≤ 1) (hP : 4 ≤ P) (h₂ : 0 < n₂ ∧ n₂ ≤ a)
    (h₃ : 0 < n₃ ∧ n₃ ≤ a) (hmin : min n₂ n₃ ≤ a ^ P) :
    0 < restartShearAmplitudeBudget a n₂ n₃ ∧ restartShearAmplitudeBudget a n₂ n₃ ≤ 800 * a := by
  have hp : a ^ P ≤ a ^ (4 : ℕ) := by
    simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_ge ha.1 ha.2 hP
  have hprod : n₂ * n₃ ≤ a * a ^ 4 := by
    rcases min_le_iff.mp hmin with hsmall | hsmall
    · exact (mul_le_mul (hsmall.trans hp) h₃.2 h₃.1.le (by positivity)).trans_eq (mul_comm _ _)
    · exact mul_le_mul h₂.2 (hsmall.trans hp) h₃.1.le ha.1.le
  refine ⟨by dsimp [restartShearAmplitudeBudget]; positivity [ha.1, h₂.1, h₃.1], ?_⟩
  calc
    _ = 800 * (n₂ * n₃) / a ^ 4 := by unfold restartShearAmplitudeBudget; ring
    _ ≤ 800 * (a * a ^ 4) / a ^ 4 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (by norm_num)) (by positivity)
    _ = _ := by field_simp

/-- Both small-wall orderings produce one measurable family of admissible era curves with a prescribed budget cap. -/
theorem solution :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P → ∀ Bstar : ℝ, 0 < Bstar →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 128) →
          let s := q / 2 * Real.log (1 / a)
          Measurable (fun p : restartShearCommonLabelSet ε a P × Icc a (2 * a) =>
            (restartShearAmplitudeBudget a p.1.val.1 p.1.val.2,
              restartShearReturnState h s p.1.val.1 p.1.val.2 p.2)) ∧
          ∀ n₂ n₃ : ℝ, (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
            min n₂ n₃ ≤ a ^ P →
            restartShearAmplitudeBudget a n₂ n₃ ∈ Ioc 0 Bstar ∧
            (restartShearEraCurve h s n₂ n₃ a).Admissible (restartShearAmplitudeBudget a n₂ n₃) ∧
            ∀ ρ ∈ Icc a (2 * a), restartShearReturnPhase h s n₂ n₃ ρ ∈ Ioo 0 1 ∧
              DifferentiableAt ℝ (restartShearReturnPhase h s n₂ n₃) ρ ∧
              1 / (4 * Real.sqrt 3) ≤ deriv (restartShearReturnPhase h s n₂ n₃) ρ ∧
              (restartShearEraCurve h s n₂ n₃ a).state (2 / restartShearReturnPhase h s n₂ n₃ ρ) =
                restartShearReturnState h s n₂ n₃ ρ := by
  obtain ⟨hE, hhE, HE⟩ := exists_restartShearReturn_common_extension
  obtain ⟨hA, hhA, HA⟩ := exists_restartShearReturn_common_bounds
  obtain ⟨hF, hhF, HF⟩ := exists_restartShearReturn_common_phase
  obtain ⟨hM, hhM, HM⟩ := exists_restartShearReturn_common_extension_measurable
  refine ⟨min hE (min hA (min hF hM)), lt_min hhE (lt_min hhA (lt_min hhF hhM)), ?_⟩
  intro h hh q D P hq hD hP Bs hBs
  have hh' := hh.2.trans (min_le_right _ _)
  have hh'' := hh'.trans (min_le_right _ _)
  obtain ⟨aE, haE, HAE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨aA, haA, HAA⟩ := HA h ⟨hh.1, hh'.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨_, _, HFC⟩ := HF h ⟨hh.1, hh''.trans (min_le_left _ _)⟩ q D hq hD
  obtain ⟨aF, haF, HAF⟩ := HFC P hP
  obtain ⟨aM, haM, HAM⟩ := HM h ⟨hh.1, hh''.trans (min_le_right _ _)⟩ q D P hq hD hP
  refine ⟨min aE (min aA (min aF (min aM (min (Bs / 800) (1 / 384))))),
    lt_min haE (lt_min haA (lt_min haF (lt_min haM
      (lt_min (div_pos hBs (by norm_num)) (by norm_num))))), ?_⟩
  intro a ha ε hε s
  have ha' := ha.2.trans (min_le_right _ _)
  have ha'' := ha'.trans (min_le_right _ _)
  have ha''' := ha''.trans (min_le_right _ _)
  have harest := ha'''.trans (min_le_right _ _)
  have haB : a ≤ Bs / 800 := harest.trans (min_le_left _ _)
  have hasmall : a ≤ 1 / 384 := harest.trans (min_le_right _ _)
  have hBm : Measurable (fun p : restartShearCommonLabelSet ε a P × Icc a (2 * a) =>
      restartShearAmplitudeBudget a p.1.val.1 p.1.val.2) := by
    unfold restartShearAmplitudeBudget
    fun_prop
  refine ⟨hBm.prodMk (HAM a ⟨ha.1, ha'''.trans (min_le_left _ _)⟩ ε hε).1, ?_⟩
  intro n₂ n₃ h₂ h₃ hmin
  have hweak : 2 * ε * a ≤ a := mul_le_of_le_one_left ha.1.le (by linarith only [hε.2] : 2 * ε ≤ 1)
  have HB := restartShearAmplitudeBudget_le_of_min ⟨ha.1, hasmall.trans (by norm_num)⟩
    (by linarith only [hD, hP] : 4 ≤ P) ⟨h₂.1, h₂.2.trans hweak⟩ ⟨h₃.1, h₃.2.trans hweak⟩ hmin
  have hbudget : restartShearAmplitudeBudget a n₂ n₃ ∈ Ioc 0 Bs :=
    ⟨HB.1, HB.2.trans (by simpa only [mul_comm] using (le_div_iff₀ (by norm_num : (0 : ℝ) < 800)).mp haB)⟩
  obtain ⟨hu, hw, Hmatch, Hbound⟩ := HAE a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ hmin
  refine ⟨hbudget, ?_, ?_⟩
  · intro k _
    obtain ⟨hup, hwp, hsum, hdu, hdw⟩ := Hbound k
    exact ⟨hup, hwp, hsum, hu.contDiffAt, hw.contDiffAt, hdu, hdw⟩
  · intro ρ hρ
    obtain ⟨_, _, _, _, _, hklo, _⟩ := HAA a ⟨ha.1, ha'.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ hmin ρ hρ
    obtain ⟨hdf, _, _, hdlo, _⟩ := HAF a ⟨ha.1, ha''.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ hmin ρ hρ
    have hkfour : 4 ≤ restartShearReturnState h s n₂ n₃ ρ 0 := (show 4 ≤ 1 / (96 * a) by
      apply (le_div_iff₀ (by positivity [ha.1])).mpr
      linarith only [hasmall]).trans hklo
    have hkpos : 0 < restartShearReturnState h s n₂ n₃ ρ 0 := by linarith only [hkfour]
    refine ⟨⟨div_pos (by norm_num) hkpos, (div_lt_one hkpos).mpr (by linarith only [hkfour])⟩, hdf, hdlo, ?_⟩
    have hrec : 2 / restartShearReturnPhase h s n₂ n₃ ρ = restartShearReturnState h s n₂ n₃ ρ 0 := by
      change 2 / (2 / restartShearReturnState h s n₂ n₃ ρ 0) = _
      field_simp
    rw [hrec]
    funext i
    fin_cases i
    · rfl
    · exact (Hmatch ρ hρ).1
    · exact (Hmatch ρ hρ).2.1
