-- Prove2me | solution 1 for BianchiIX.exists_restartShearTail_entrance_phase
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:59:41.407491+00:00
-- url     : https://prove2.me/submissions/a4987b93-61d6-4a47-95ee-6068a836ed98

import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_EntranceRegion
import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_ShearTransportData
import Theorems.Thm_BianchiIX_entranceReturn_region
import Theorems.Thm_BianchiIX_entranceReturn_regular
import Theorems.Thm_BianchiIX_exists_entrance_physical_curve_bounds
import Theorems.Thm_BianchiIX_exists_restartShearTail_entrance_inputs
import Theorems.Thm_BianchiIX_exists_restartShearTail_projection_phase
import Theorems.Thm_BianchiIX_reciprocal_radial_bounds
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
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Log.Basic

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

private theorem BianchiIX.exists_entrance_log_weighted_radius :
    ∃ C > (0 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧
      ∀ (Y : ℝ → ProjectiveState) (ρ D L : ℝ),
      let y := Y ρ
      let k := coreRadius (y 0) (y 2)
      let κ := fun r => coreRadius (entranceReturnState (Y r) 0) (entranceReturnState (Y r) 2)
      let K := fun r => coreRadius (Y r 0) (Y r 2)
      DifferentiableAt ℝ Y ρ → 0 ≤ D → 1 ≤ L → 8 ≤ k → 1 ≤ y 0 →
      (0 < y 1 ∧ y 1 ≤ ε) → (0 < y 2 ∧ y 2 < 1) → (0 < y 3 ∧ y 3 ≤ ε) →
      L * (y 1 + y 3) ≤ 1 →
      |deriv (fun r => Y r 0) ρ| ≤ D * k ^ 2 →
      (∀ i : Fin 4, i ≠ 0 → |deriv (fun r => Y r i) ρ| ≤ D * L * k * y i) →
      DifferentiableAt ℝ κ ρ ∧ DifferentiableAt ℝ K ρ ∧
      |κ ρ - k| ≤ C / k ∧ |deriv κ ρ - deriv K ρ| ≤ C * D * k := by
  obtain ⟨A, hA, ε, hε, hεsmall, HA⟩ := exists_entrance_physical_curve_bounds
  refine ⟨3 * A, by positivity, ε, hε, hεsmall, ?_⟩
  intro Y ρ D L y k κ K HY hD hL hk hm hu hv hw hsmall hd0 hdwall
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hL0 : 0 ≤ L := by linarith only [hL]
  have Hd0 : |deriv (fun r => Y r 0) ρ| ≤ (D * L) * k ^ 2 := hd0.trans (by
    nlinarith only [mul_le_mul_of_nonneg_left hL (mul_nonneg hD (sq_nonneg k))])
  obtain ⟨Hκ, HK, Hval, Hder⟩ := HA Y ρ (D * L) HY (mul_nonneg hD hL0)
    (by linarith only [hk]) hm hu hv hw Hd0 hdwall
  let b := y 1 + y 3
  have hb0 : 0 ≤ b := add_nonneg hu.1.le hw.1.le
  have hb1 : b ≤ 1 := by
    have H := mul_le_mul_of_nonneg_right hL hb0
    change L * b ≤ 1 at hsmall
    linarith only [H, hsmall]
  have hb2 : b ^ 2 ≤ 1 := by nlinarith only [hb0, hb1]
  have hv2 : (y 2) ^ 2 ≤ 1 := by nlinarith only [hv.1, hv.2]
  have Henergy : y 1 * y 2 + (y 2) ^ 2 * b ^ 2 ≤ b + b ^ 2 := by
    have H0 := mul_le_mul_of_nonneg_left hv.2.le hu.1.le
    have H1 := mul_le_mul_of_nonneg_right hv2 (sq_nonneg b)
    dsimp only [b] at *
    nlinarith only [H0, H1, hw.1]
  have HLb2 : L * b ^ 2 ≤ 1 := by
    have H := mul_le_mul_of_nonneg_right hsmall hb0
    change L * (y 1 + y 3) * b ≤ 1 * b at H
    dsimp only [b] at *
    nlinarith only [H, hb1]
  have HE : L * (y 1 * y 2 + (y 2) ^ 2 * b ^ 2) ≤ 2 := by
    have H := mul_le_mul_of_nonneg_left Henergy hL0
    change L * b ≤ 1 at hsmall
    linarith only [H, hsmall, HLb2]
  refine ⟨Hκ, HK, ?_, ?_⟩
  · apply Hval.trans
    change A * (b ^ 2 + (y 1 * y 2 + (y 2) ^ 2 * b ^ 2)) / k ≤ _
    apply div_le_div_of_nonneg_right _ hk0
    nlinarith only [mul_le_mul_of_nonneg_left Henergy hA.le,
      mul_le_mul_of_nonneg_left hb1 hA.le, mul_le_mul_of_nonneg_left hb2 hA.le]
  · have HB : L * (b ^ 2 + k * (y 1 * y 2 + (y 2) ^ 2 * b ^ 2)) ≤ 3 * k := by
      have H := mul_le_mul_of_nonneg_left HE hk0
      nlinarith only [H, HLb2, hk]
    have H := mul_le_mul_of_nonneg_left HB (mul_nonneg hA.le hD)
    change |deriv κ ρ - deriv K ρ| ≤ A * (D * L) *
      (b ^ 2 + k * (y 1 * y 2 + (y 2) ^ 2 * b ^ 2)) at Hder
    nlinarith only [Hder, H]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartShearTail_entrance_radius :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D : ℝ, 2 < q → 2 < D → ∃ C > (0 : ℝ),
        ∀ P : ℝ, 6 * D + 2 < P → ∃ astar > (0 : ℝ),
          ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
            (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let Y := restartShearTailProjectiveEntry h a q ζ ν (shearTailTime a D)
            let k := fun r => coreRadius (Y r 0) (Y r 2)
            let κ := fun r => coreRadius (entranceReturnState (Y r) 0) (entranceReturnState (Y r) 2)
            entranceReturnValid (Y ρ) ∧ ContDiffAt ℝ 2 entranceReturnTime (Y ρ) ∧
            ContDiffAt ℝ 2 entranceReturnState (Y ρ) ∧
            DifferentiableAt ℝ κ ρ ∧ DifferentiableAt ℝ k ρ ∧
            1 / (48 * a) ≤ κ ρ ∧ κ ρ ≤ 128 / a ∧ 1 / (48 * a) ≤ k ρ ∧
            |κ ρ - k ρ| ≤ C * a ∧ |deriv κ ρ - deriv k ρ| ≤ C / a ∧
            |deriv k ρ| ≤ 6144 / a ^ 2 := by
  obtain ⟨A, hA, δ, hδ, hδsmall, HA⟩ := exists_entrance_log_weighted_radius
  obtain ⟨hI, hhI, HI⟩ := exists_restartShearTail_entrance_inputs
  obtain ⟨hF, hhF, HF⟩ := exists_restartShearTail_projection_phase
  refine ⟨min hI hF, lt_min hhI hhF, ?_⟩
  intro h hh q D hq hD
  obtain ⟨B, hB, HB⟩ := HI h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D hq hD
  obtain ⟨_, _, HΦ⟩ := HF h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D hq hD
  let C := 24 * A + 64 * A * B + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hCA : 24 * A ≤ C := by dsimp only [C]; linarith only [mul_pos hA hB]
  have hCAB : 64 * A * B ≤ C := by dsimp only [C]; linarith only [hA]
  refine ⟨C, hC, ?_⟩
  intro P hP
  obtain ⟨aI, haI, HAI⟩ := HB P hP δ ⟨hδ, hδsmall⟩
  obtain ⟨aF, haF, HAF⟩ := HΦ P hP
  refine ⟨min aI aF, lt_min haI haF, ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ Y k κ
  obtain ⟨HY, hk8, hklo, hkhi, hm, hu, hv, hw, Hsmall, Hdm, Hdwall⟩ :=
    HAI a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, _, HfD, _, _, Hflo, Hfhi⟩ :=
    HAF a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  let f := restartShearTailProjectionPhase h a q ζ ν (shearTailTime a D)
  have hk0 : 0 < k ρ := by change 8 ≤ k ρ at hk8; linarith only [hk8]
  have hk' : 7 / 4 ≤ k ρ := by change 8 ≤ k ρ at hk8; linarith only [hk8]
  have hu' : 0 ≤ Y ρ 1 ∧ Y ρ 1 ≤ 1 / 10000 := ⟨hu.1.le, hu.2.trans hδsmall⟩
  have hw' : 0 ≤ Y ρ 3 ∧ Y ρ 3 ≤ 1 / 10000 := ⟨hw.1.le, hw.2.trans hδsmall⟩
  obtain ⟨Hvalid, Htime, Hstate, _⟩ := entranceReturn_regular hk' hm.le hu' hv hw'
  have Hreg := entranceReturn_region hk' hm.le hu' hv hw' _ ⟨Hvalid.1.1.1.le, le_rfl⟩
  change entranceRegion (k ρ) (entranceReturnState (Y ρ)) at Hreg
  have Hκscale : 99 / 100 * k ρ ≤ κ ρ ∧ κ ρ ≤ 101 / 100 * k ρ := by
    have H := abs_le.mp Hreg.2.1
    change -(k ρ / 100) ≤ κ ρ - k ρ ∧ κ ρ - k ρ ≤ k ρ / 100 at H
    constructor <;> linarith only [H.1, H.2]
  have HL : 1 ≤ 1 + |Real.log a| := by linarith only [abs_nonneg (Real.log a)]
  obtain ⟨HκD, HkD, Hvalue, Hder⟩ := HA Y ρ B (1 + |Real.log a|) HY hB.le HL hk8 hm.le hu hv hw
    Hsmall Hdm Hdwall
  have HKlo : 1 / (48 * a) ≤ k ρ := by
    exact (div_le_div_of_nonneg_left (by norm_num) (by positivity [ha.1])
      (by linarith only [ha.1])).trans hklo
  have Hκlo : 1 / (48 * a) ≤ κ ρ := by
    calc
      _ = (1 / 2) * (1 / (24 * a)) := by ring
      _ ≤ (1 / 2) * k ρ := mul_le_mul_of_nonneg_left hklo (by norm_num)
      _ ≤ _ := by linarith only [Hκscale.1, hk0]
  have Hκhi : κ ρ ≤ 128 / a := by
    calc
      _ ≤ 2 * k ρ := by linarith only [Hκscale.2, hk0]
      _ ≤ 2 * (64 / a) := mul_le_mul_of_nonneg_left hkhi (by norm_num)
      _ = _ := by ring
  have HV : |κ ρ - k ρ| ≤ C * a := Hvalue.trans (by
    calc
      _ ≤ A / (1 / (24 * a)) := div_le_div_of_nonneg_left hA.le (by positivity [ha.1]) hklo
      _ = 24 * A * a := by field_simp [ha.1.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_right hCA ha.1.le)
  have HD : |deriv κ ρ - deriv k ρ| ≤ C / a := Hder.trans (by
    calc
      _ ≤ A * B * (64 / a) := mul_le_mul_of_nonneg_left hkhi (mul_nonneg hA.le hB.le)
      _ = (64 * A * B) / a := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hCAB ha.1.le)
  have hf0 : 0 < f ρ := div_pos (by norm_num) hk0
  have Hfscale : a / 32 ≤ f ρ := by
    calc
      _ = 2 / (64 / a) := by field_simp [ha.1.ne']; ring
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hk0 hkhi
  have Hfabs : |deriv f ρ| ≤ 3 := by
    have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := Real.one_le_sqrt.mpr (by norm_num)
    have hsqrt0 : 0 < Real.sqrt (3 : ℝ) := by positivity
    rw [abs_of_nonneg (by exact (by positivity : 0 ≤ 1 / (4 * Real.sqrt (3 : ℝ))).trans Hflo)]
    have H := div_le_self (by norm_num : (0 : ℝ) ≤ 2) hsqrt1
    linarith only [H, Hfhi]
  have heq : k = fun r => 2 / f r := by
    funext r
    change coreRadius (Y r 0) (Y r 2) = 2 / (2 / coreRadius (Y r 0) (Y r 2))
    simp
  have Hkd : |deriv k ρ| ≤ 6144 / a ^ 2 := by
    rw [heq, deriv_const_div 2 HfD hf0.ne', abs_div, abs_mul, abs_neg,
      abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_nonneg (sq_nonneg (f ρ))]
    calc
      _ ≤ (2 * 3) / (f ρ) ^ 2 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left Hfabs (by norm_num)) (sq_nonneg _)
      _ ≤ (2 * 3) / (a / 32) ^ 2 := div_le_div_of_nonneg_left (by norm_num)
        (by positivity [ha.1]) (pow_le_pow_left₀ (by positivity [ha.1]) Hfscale 2)
      _ = _ := by ring
  exact ⟨Hvalid, Htime, Hstate, HκD, HkD, Hκlo, Hκhi, HKlo, HV, HD, Hkd⟩

end
end

/-- The first upward entrance after the long tail has the original reference phase and nondegenerate radius slope. -/
theorem solution :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D : ℝ, 2 < q → 2 < D → ∃ C > (0 : ℝ),
        ∀ P : ℝ, 6 * D + 2 < P → ∃ astar > (0 : ℝ),
          ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
            (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let Φ := restartShearTailEntrancePhase h a q D ζ ν
            let F := restartShearTailEntranceRadius h a q D ζ ν
            let f₀ := fun r => restartReferenceRadialPhase h (restartShearCurve 1 ζ ν r)
            entranceReturnValid (restartShearTailProjectiveEntry h a q ζ ν (shearTailTime a D) ρ) ∧
            DifferentiableAt ℝ Φ ρ ∧ |Φ ρ - f₀ ρ| ≤ C * a ^ 2 ∧
            |deriv Φ ρ - deriv f₀ ρ| ≤ C * a ∧
            1 / (4 * Real.sqrt 3) ≤ deriv Φ ρ ∧ deriv Φ ρ ≤ 2 / Real.sqrt 3 + 1 ∧
            DifferentiableAt ℝ F ρ ∧ 1 / (48 * a) ≤ F ρ ∧ F ρ ≤ 128 / a ∧
            1 / (36864 * a ^ 2) ≤ -deriv F ρ ∧ -deriv F ρ ≤ 24576 / a ^ 2 := by
  obtain ⟨hR, hhR, HR⟩ := exists_restartShearTail_entrance_radius
  obtain ⟨hG, hhG, HG⟩ := exists_restartShearTail_projection_phase
  refine ⟨min hR (min hG (1 / 16)), lt_min hhR (lt_min hhG (by norm_num)), ?_⟩
  intro h hh q D hq hD
  obtain ⟨B, hB, HB⟩ := HR h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D hq hD
  obtain ⟨K, hK, HK⟩ := HG h ⟨hh.1, hh.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩ q D hq hD
  let A := 2 * 48 ^ 2 * B + 4 * 6144 * 48 ^ 3 * B
  let C := A + K
  have hA : 0 < A := by dsimp only [A]; positivity
  have hC : 0 < C := add_pos hA hK
  have hvalue : 2 * 48 ^ 2 * B ≤ A := by dsimp only [A]; linarith only [hB]
  refine ⟨C, hC, ?_⟩
  intro P hP
  obtain ⟨aR, haR, HAR⟩ := HB P hP
  obtain ⟨aG, haG, HAG⟩ := HK P hP
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := by positivity
  have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := Real.one_le_sqrt.mpr (by norm_num)
  refine ⟨min aR (min aG (min 1 (1 / (4 * Real.sqrt 3 * C)))),
    lt_min haR (lt_min haG (lt_min zero_lt_one (by positivity))), ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ Φ F f₀
  let Y := restartShearTailProjectiveEntry h a q ζ ν (shearTailTime a D)
  let k := fun r => coreRadius (Y r 0) (Y r 2)
  let f := restartShearTailProjectionPhase h a q ζ ν (shearTailTime a D)
  have ha1 : a ≤ 1 := ha.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨Hvalid, _, _, HFD, HkD, HFlo, HFhi, Hklo, Hrv, Hrd, Hkd⟩ :=
    HAR a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, _, HfD, Hfv, Hfd, _, _⟩ :=
    HAG a ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩ ε ζ ν hε hζ hν ρ hρ
  have HF0 : 0 < F ρ := (by positivity [ha.1] : 0 < 1 / (48 * a)).trans_le HFlo
  have HΦD : DifferentiableAt ℝ Φ ρ :=
    ((hasDerivAt_const ρ (2 : ℝ)).div HFD.hasDerivAt HF0.ne').differentiableAt
  have Hrv' : |F ρ - k ρ| ≤ B := Hrv.trans (mul_le_of_le_one_right hB.le ha1)
  obtain ⟨_, HV, HD⟩ := reciprocal_radial_comparison ha.1 (by norm_num : (0 : ℝ) < 48)
    (by norm_num : (0 : ℝ) ≤ 6144) HFD HkD HFlo Hklo Hrv' Hkd Hrd
  change |Φ ρ - f ρ| ≤ 2 * 48 ^ 2 * B * a ^ 2 at HV
  change |deriv (fun r => Φ r - f r) ρ| ≤ A * a at HD
  rw [deriv_fun_sub HΦD HfD] at HD
  have HV' := HV.trans (mul_le_mul_of_nonneg_right hvalue (sq_nonneg a))
  have Hval : |Φ ρ - f₀ ρ| ≤ C * a ^ 2 :=
    (abs_sub_le _ _ _).trans ((add_le_add HV' Hfv).trans_eq (by dsimp only [C]; ring))
  have Hder : |deriv Φ ρ - deriv f₀ ρ| ≤ C * a :=
    (abs_sub_le _ _ _).trans ((add_le_add HD Hfd).trans_eq (by dsimp only [C]; ring))
  have Href := restartReferenceRadialPhase_shear_derivative
    ⟨hh.1.le, hh.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
    ha.1 hρ (by norm_num : |(1 : ℝ)| = 1) ⟨hε.1, by linarith only [hε.2]⟩
    ⟨hζ.1.le, hζ.2.2⟩ ⟨hν.1.le, hν.2⟩
  have hCa : C * a ≤ 1 / (4 * Real.sqrt 3) := by
    have H := (le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt 3 * C)).mp
      (ha.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
    apply (le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt 3)).mpr
    nlinarith only [H]
  have hquarter : 1 / (4 * Real.sqrt 3) ≤ 1 :=
    (div_le_one (by positivity : 0 < 4 * Real.sqrt 3)).mpr (by linarith only [hsqrt1])
  have Hlo : 1 / (4 * Real.sqrt 3) ≤ deriv Φ ρ := by
    have he : 1 / (2 * Real.sqrt 3) = 2 * (1 / (4 * Real.sqrt 3)) := by ring
    rw [he] at Href
    linarith only [(abs_le.mp Hder).1, Href.2.1, hCa]
  have Hhi : deriv Φ ρ ≤ 2 / Real.sqrt 3 + 1 := by
    linarith only [(abs_le.mp Hder).2, Href.2.2, hCa, hquarter]
  have HΦlo : (a / 4) / 16 ≤ Φ ρ := by
    calc
      _ = 2 / (128 / a) := by field_simp [ha.1.ne']; ring
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) HF0 HFhi
  have HΦhi : Φ ρ ≤ 384 * (a / 4) := by
    calc
      _ ≤ 2 / (1 / (48 * a)) := div_le_div_of_nonneg_left (by norm_num) (by positivity [ha.1]) HFlo
      _ = _ := by field_simp [ha.1.ne']; ring
  have HDlo : 1 / 8 ≤ deriv Φ ρ := by
    have hsqrt2 : Real.sqrt (3 : ℝ) ≤ 2 := by
      nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), hsqrt]
    exact ((le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt 3)).mpr
      (by linarith only [hsqrt2])).trans Hlo
  have HDhi : deriv Φ ρ ≤ 3 := by
    have H := div_le_self (by norm_num : (0 : ℝ) ≤ 2) hsqrt1
    linarith only [H, Hhi]
  obtain ⟨_, _, _, HFlod, HFhid⟩ := reciprocal_radial_bounds (by positivity [ha.1] : 0 < a / 4)
    (by norm_num : (0 : ℝ) ≤ 3) HΦD HΦlo HΦhi HDlo HDhi
  have heq : (fun r => 2 / Φ r) = F := by
    funext r
    change 2 / (2 / F r) = F r
    simp
  rw [heq] at HFlod HFhid
  refine ⟨Hvalid, HΦD, Hval, Hder, Hlo, Hhi, HFD, HFlo, HFhi, ?_, ?_⟩
  · convert! HFlod using 1
    ring
  · convert! HFhid using 1
    ring
