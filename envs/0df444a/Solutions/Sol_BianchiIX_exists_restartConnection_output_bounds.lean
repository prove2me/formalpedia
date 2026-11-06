-- Prove2me | solution 1 for BianchiIX.exists_restartConnection_output_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:51:55.198375+00:00
-- url     : https://prove2.me/submissions/111e3f3b-9918-4214-81d5-511f5646542a

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Definitions.Def_BianchiIX_Dynamics_ConnectionExistence
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturn
import Definitions.Def_BianchiIX_Dynamics_ConnectionPhysicalReturn
import Definitions.Def_BianchiIX_Dynamics_CoreConnectionChart
import Theorems.Thm_BianchiIX_connectionReturn_restart_bounds
import Theorems.Thm_BianchiIX_exists_restartFastProjectionError_bounds
import Theorems.Thm_BianchiIX_exists_restartFastProjectiveEntry_bounds
import Theorems.Thm_BianchiIX_exists_restartPartialCore_connection
import Theorems.Thm_BianchiIX_exists_restartSection_radial_approximation
import Theorems.Thm_BianchiIX_reciprocal_radial_bounds
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
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
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
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
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section
open BianchiIX
open Set

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

private theorem BianchiIX.abs_quadraticFromCoefficients_le (m : Fin 3 → ℝ) (s v : ℝ) :
    |quadraticFromCoefficients m s v| ≤ 2 * ‖m‖ * (s ^ 2 + v ^ 2) := by
  have hm (i : Fin 3) : |m i| ≤ ‖m‖ := norm_le_pi_norm m i
  have hsv : |s| * |v| ≤ s ^ 2 + v ^ 2 := by
    nlinarith only [sq_nonneg (|s| - |v|), sq_abs s, sq_abs v, sq_nonneg s, sq_nonneg v]
  calc
    _ ≤ |m 0 * s ^ 2| + |m 1 * s * v| + |m 2 * v ^ 2| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ ‖m‖ * s ^ 2 + ‖m‖ * (|s| * |v|) + ‖m‖ * v ^ 2 := by
      simp only [abs_mul, abs_sq, mul_assoc]
      gcongr
      · exact hm 0
      · exact hm 1
      · exact hm 2
    _ ≤ 2 * ‖m‖ * (s ^ 2 + v ^ 2) := by
      nlinarith only [mul_le_mul_of_nonneg_left hsv (norm_nonneg m)]

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

private theorem BianchiIX.restartQuadratic_relative_error {n : ℝ} (hn : 0 ≤ n ∧ n ≤ 1 / 16) (s v : ℝ) :
    |restartQuadratic n s v - (s ^ 2 + v ^ 2)| ≤ 8 * n * (s ^ 2 + v ^ 2) := by
  obtain ⟨ha0, ha1, hc0, hc1, hk0, hk1⟩ := restart_coefficients_small hn
  have hn2 : n ^ 2 ≤ n := by nlinarith only [hn.1, hn.2]
  have haSq := mul_self_le_mul_self (by linarith only [ha0] : 0 ≤ restartShearFactor n)
    (by linarith only [ha1] : restartShearFactor n ≤ 1 + n)
  have hcSq := mul_self_le_mul_self (by linarith only [hc0] : 0 ≤ restartWallFactor n)
    (by linarith only [hc1] : restartWallFactor n ≤ 1 + n)
  have hkSq := mul_self_le_mul_self hk0 hk1
  have hak := mul_le_mul ha1 hk1 hk0 hn.1
  let m : Fin 3 → ℝ := ![restartShearFactor n ^ 2 - 1,
    2 * restartShearFactor n * restartShearCoupling n,
    restartShearCoupling n ^ 2 + restartWallFactor n ^ 2 - 1]
  have hm : ‖m‖ ≤ 4 * n := by
    apply (pi_norm_le_iff_of_nonneg (by positivity [hn.1] : 0 ≤ 4 * n)).mpr
    intro i
    fin_cases i <;> apply abs_le.mpr <;> constructor
    · change -(4 * n) ≤ restartShearFactor n ^ 2 - 1
      nlinarith only [ha0, hn.1]
    · change restartShearFactor n ^ 2 - 1 ≤ 4 * n
      nlinarith only [haSq, hn2, hn.1]
    · change -(4 * n) ≤ 2 * restartShearFactor n * restartShearCoupling n
      nlinarith only [mul_nonneg (by linarith only [ha0] : 0 ≤ restartShearFactor n) hk0, hn.1]
    · change 2 * restartShearFactor n * restartShearCoupling n ≤ 4 * n
      nlinarith only [hak, hk1, hn2]
    · change -(4 * n) ≤ restartShearCoupling n ^ 2 + restartWallFactor n ^ 2 - 1
      nlinarith only [hc0, sq_nonneg (restartShearCoupling n), hn.1]
    · change restartShearCoupling n ^ 2 + restartWallFactor n ^ 2 - 1 ≤ 4 * n
      nlinarith only [hcSq, hkSq, hn2]
  have heq : restartQuadratic n s v - (s ^ 2 + v ^ 2) = quadraticFromCoefficients m s v := by
    dsimp [restartQuadratic, quadraticFromCoefficients, m]
    ring
  rw [heq]
  exact (abs_quadraticFromCoefficients_le m s v).trans (by
    nlinarith only [mul_le_mul_of_nonneg_right hm (add_nonneg (sq_nonneg s) (sq_nonneg v))])

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartQuadratic_upper {n : ℝ} (hn : 0 ≤ n ∧ n ≤ 1 / 16) (s v : ℝ) :
    restartQuadratic n s v ≤ 2 * (s ^ 2 + v ^ 2) := by
  have H := (le_abs_self _).trans (restartQuadratic_relative_error hn s v)
  have Hn := mul_le_mul_of_nonneg_right hn.2 (add_nonneg (sq_nonneg s) (sq_nonneg v))
  nlinarith only [H, Hn, sq_nonneg s, sq_nonneg v]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.sqrt_restartQuadratic_le_radius {n r s v : ℝ} (hn : 0 ≤ n ∧ n ≤ 1 / 16)
    (hr : 0 ≤ r) (hs : |s| ≤ r) (hv : |v| ≤ 2 * r) :
    Real.sqrt (restartQuadratic n s v) ≤ 4 * r := by
  have hs2 := mul_self_le_mul_self (abs_nonneg s) hs
  have hv2 := mul_self_le_mul_self (abs_nonneg v) hv
  have HJ : 0 ≤ restartQuadratic n s v := add_nonneg (sq_nonneg _) (sq_nonneg _)
  nlinarith only [restartQuadratic_upper hn s v, Real.sq_sqrt HJ, Real.sqrt_nonneg (restartQuadratic n s v),
    hs2, hv2, sq_abs s, sq_abs v, hr, sq_nonneg r]

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

private theorem BianchiIX.hasDerivAt_restartRadialCurve (θ ζ ρ : ℝ) :
    HasDerivAt (restartRadialCurve θ ζ) (restartRadialDirection θ) ρ := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [restartRadialCurve, restartRadialDirection] using (hasDerivAt_id ρ).const_mul θ
  · convert! hasDerivAt_id ρ using 1
  · simpa [restartRadialCurve, restartRadialDirection] using hasDerivAt_const ρ ζ

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartRadialDirection_norm_le {θ L : ℝ} (hL : 0 ≤ L) (hθ : |θ| ≤ L) :
    ‖restartRadialDirection θ‖ ≤ L + 1 := by
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ L + 1)).mpr
  intro i
  fin_cases i
  · change |θ| ≤ L + 1
    linarith only [hθ]
  · change |(1 : ℝ)| ≤ L + 1
    rw [abs_one]
    linarith only [hL]
  · change |(0 : ℝ)| ≤ L + 1
    rw [abs_zero]
    positivity

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartRadialCurve_annulus {r ρ θ ζ L : ℝ} (hr : 0 < r)
    (hρ : ρ ∈ Icc r (2 * r)) (hL : 0 ≤ L) (hθ : |θ| ≤ L)
    (hζ : 0 ≤ ζ ∧ ζ ≤ r / 9) :
    ‖restartRadialCurve θ ζ ρ‖ ≤ (2 * (L + 1)) * r ∧
      r / 2 ≤ restartRadialNorm (restartRadialCurve θ ζ ρ) := by
  have hρ0 : 0 < ρ := hr.trans_le hρ.1
  constructor
  · apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (2 * (L + 1)) * r)).mpr
    intro i
    fin_cases i
    · change |θ * ρ| ≤ _
      rw [abs_mul, abs_of_pos hρ0]
      have H := mul_le_mul hθ hρ.2 hρ0.le hL
      nlinarith only [H, hr]
    · change |ρ| ≤ _
      rw [abs_of_pos hρ0]
      nlinarith only [hρ.2, mul_nonneg hL hr.le]
    · change |ζ| ≤ _
      rw [abs_of_nonneg hζ.1]
      nlinarith only [hζ.2, hr, mul_nonneg hL hr.le]
  · have hdiff : 0 ≤ ρ - ζ := by linarith only [hρ.1, hζ.2, hr]
    have H := Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg (θ * ρ)) :
      (ρ - ζ) ^ 2 ≤ (θ * ρ) ^ 2 + (ρ - ζ) ^ 2)
    rw [Real.sqrt_sq hdiff] at H
    change r / 2 ≤ Real.sqrt ((θ * ρ) ^ 2 + (ρ - ζ) ^ 2)
    linarith only [H, hρ.1, hζ.2, hr]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartReferenceRadialPhase_curve (h θ ζ ρ : ℝ) :
    restartReferenceRadialPhase h (restartRadialCurve θ ζ ρ) =
      phaseNorm ((restartShearFactor h * θ + restartShearCoupling h) * ρ -
        restartShearCoupling h * ζ) (restartWallFactor h * ρ - restartWallFactor h * ζ) /
          Real.sqrt 3 := by
  change Real.sqrt ((restartShearFactor h * (θ * ρ) + restartShearCoupling h * (ρ - ζ)) ^ 2 +
    (restartWallFactor h * (ρ - ζ)) ^ 2) / Real.sqrt 3 = _
  unfold phaseNorm
  congr 2
  ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartReferenceRadialPhase_curve_derivative {h θ ζ ρ L : ℝ}
    (hh : 0 ≤ h ∧ h ≤ 1 / 16) (_hL : 0 ≤ L) (hθ : |θ| ≤ L)
    (hρ : 0 < ρ) (hζ : 0 ≤ ζ ∧ ζ ≤ ρ / 9) :
    DifferentiableAt ℝ (fun x => restartReferenceRadialPhase h (restartRadialCurve θ ζ x)) ρ ∧
      1 / (2 * Real.sqrt 3) ≤
        deriv (fun x => restartReferenceRadialPhase h (restartRadialCurve θ ζ x)) ρ ∧
      deriv (fun x => restartReferenceRadialPhase h (restartRadialCurve θ ζ x)) ρ ≤
        (2 * L + 3) / Real.sqrt 3 := by
  obtain ⟨ha0, ha1, hc0, hc1, hk0, hk1⟩ := restart_coefficients_small hh
  let a := restartShearFactor h
  let c := restartWallFactor h
  let k := restartShearCoupling h
  have ha : 1 ≤ a ∧ a ≤ 2 := by dsimp only [a]; constructor <;> linarith only [ha0, ha1, hh.2]
  have hc : 1 ≤ c ∧ c ≤ 2 := by dsimp only [c]; constructor <;> linarith only [hc0, hc1, hh.2]
  have hk : 0 ≤ k ∧ k ≤ 1 := ⟨hk0, hk1.trans (by linarith only [hh.2])⟩
  have hP : 1 ≤ phaseNorm (a * θ + k) c := by
    have H := phaseNorm_ge (b := a * θ + k) (by linarith only [hc.1] : 0 ≤ c)
    have heq : phaseNorm c (a * θ + k) = phaseNorm (a * θ + k) c := by
      simp only [phaseNorm, add_comm]
    rw [heq] at H
    exact hc.1.trans H
  have hQ : phaseNorm k c ≤ 3 := by
    have H := phaseNorm_le_abs_add k c
    rw [abs_of_nonneg hk.1, abs_of_nonneg (by linarith only [hc.1] : 0 ≤ c)] at H
    linarith only [H, hk.2, hc.2]
  have hPupper : phaseNorm (a * θ + k) c ≤ 2 * L + 3 := by
    have H := phaseNorm_le_abs_add (a * θ + k) c
    have Hθ := mul_le_mul ha.2 hθ (abs_nonneg θ) (by norm_num : (0 : ℝ) ≤ 2)
    have Hsum := abs_add_le (a * θ) k
    rw [abs_mul, abs_of_nonneg (by linarith only [ha.1] : 0 ≤ a), abs_of_nonneg hk.1] at Hsum
    rw [abs_of_nonneg (by linarith only [hc.1] : 0 ≤ c)] at H
    linarith only [H, Hθ, Hsum, hk.2, hc.2]
  have hsmall : 3 * ζ * phaseNorm k c ≤ ρ * phaseNorm (a * θ + k) c := by
    have H := mul_le_mul_of_nonneg_left hQ (show 0 ≤ 3 * ζ by positivity [hζ.1])
    have H' := mul_le_mul_of_nonneg_left hP hρ.le
    nlinarith only [H, H', hζ.2]
  obtain ⟨v, Hv, hvlow, hvup⟩ := hasDerivAt_phaseNorm_affine_bounds
    (show 0 < phaseNorm (a * θ + k) c by linarith only [hP]) hρ hζ.1 hsmall
  have Href : HasDerivAt (fun x => restartReferenceRadialPhase h (restartRadialCurve θ ζ x))
      (v / Real.sqrt 3) ρ := by
    simpa only [restartReferenceRadialPhase_curve, a, c, k] using Hv.div_const (Real.sqrt 3)
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨Href.differentiableAt, ?_, ?_⟩ <;> rw [Href.deriv]
  · have H : (1 : ℝ) / 2 ≤ v := by linarith only [hP, hvlow]
    calc
      _ = (1 / 2) / Real.sqrt 3 := by ring
      _ ≤ v / Real.sqrt 3 := div_le_div_of_nonneg_right H hsqrt.le
  · exact div_le_div_of_nonneg_right (hvup.trans hPupper) hsqrt.le

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartFastRadialPhase_derivative {h T θ ζ ρ L ε : ℝ}
    (hh : 0 ≤ h ∧ h ≤ 1 / 16) (hL : 0 ≤ L) (hθ : |θ| ≤ L)
    (hρ : 0 < ρ) (hζ : 0 ≤ ζ ∧ ζ ≤ ρ / 9) (hε : 0 ≤ ε)
    (HD : DifferentiableAt ℝ (restartSectionRadialError h T) (restartRadialCurve θ ζ ρ))
    (HB : ‖fderiv ℝ (restartSectionRadialError h T) (restartRadialCurve θ ζ ρ)‖ ≤ ε) :
    DifferentiableAt ℝ (restartFastRadialPhase h T θ ζ) ρ ∧
      |deriv (restartFastRadialPhase h T θ ζ) ρ -
        deriv (fun x => restartReferenceRadialPhase h (restartRadialCurve θ ζ x)) ρ| ≤ ε * (L + 1) := by
  have Href := (restartReferenceRadialPhase_curve_derivative hh hL hθ hρ hζ).1.hasDerivAt
  have Herr := HD.hasFDerivAt.comp_hasDerivAt ρ (hasDerivAt_restartRadialCurve θ ζ ρ)
  have Hsum : HasDerivAt (restartFastRadialPhase h T θ ζ)
      ((fderiv ℝ (restartSectionRadialError h T) (restartRadialCurve θ ζ ρ)) (restartRadialDirection θ) +
        deriv (fun x => restartReferenceRadialPhase h (restartRadialCurve θ ζ x)) ρ) ρ := by
    convert! Herr.add Href using 1
    ext x
    simp only [Function.comp_apply, Pi.add_apply, restartSectionRadialError, restartFastRadialPhase,
      sub_add_cancel]
  refine ⟨Hsum.differentiableAt, ?_⟩
  rw [Hsum.deriv, add_sub_cancel_right]
  exact ((fderiv ℝ (restartSectionRadialError h T) (restartRadialCurve θ ζ ρ)).le_opNorm _).trans
    (mul_le_mul HB (restartRadialDirection_norm_le hL hθ) (norm_nonneg _) hε)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartFastRadialPhase_monotone :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∃ K : ℝ, 0 < K ∧ ∀ q : ℝ, 2 < q →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ r / 9) → ∀ ρ ∈ Icc r (2 * r),
            let T := q / 2 * Real.log (1 / r)
            T ∈ normalizedMaxDomain (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 ∧
            DifferentiableAt ℝ (restartFastRadialPhase h T θ ζ) ρ ∧
            |restartFastRadialPhase h T θ ζ ρ -
              restartReferenceRadialPhase h (restartRadialCurve θ ζ ρ)| ≤ K * r ^ 2 ∧
            |deriv (restartFastRadialPhase h T θ ζ) ρ -
              deriv (fun x => restartReferenceRadialPhase h (restartRadialCurve θ ζ x)) ρ| ≤ K * r ∧
            1 / (4 * Real.sqrt 3) ≤ deriv (restartFastRadialPhase h T θ ζ) ρ ∧
            deriv (restartFastRadialPhase h T θ ζ) ρ ≤ (2 * L + 3) / Real.sqrt 3 + 1 := by
  obtain ⟨h₀, hh₀, H₀⟩ := exists_restartSection_radial_approximation
  refine ⟨min h₀ (1 / 16), lt_min hh₀ (by norm_num), ?_⟩
  intro h hh L hL
  have hhsmall : 0 ≤ h ∧ h ≤ 1 / 16 := ⟨hh.1.le, hh.2.trans (min_le_right _ _)⟩
  obtain ⟨A, hA, HA⟩ := H₀ h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩
    (1 / 2) (2 * (L + 1)) (by norm_num) (by positivity)
  let K := A * (L + 1)
  have hK : 0 < K := mul_pos hA (by positivity)
  have hAK : A ≤ K := by dsimp only [K]; nlinarith only [mul_nonneg hA.le hL]
  refine ⟨K, hK, ?_⟩
  intro q hq
  obtain ⟨r₀, hr₀, Hr₀⟩ := HA q hq
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), hsqrt]
  refine ⟨min r₀ (1 / (4 * Real.sqrt 3 * K)), lt_min hr₀ (by positivity), ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  have hann := restartRadialCurve_annulus hr.1 hρ hL hθ hζ
  have H := Hr₀ r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩ (restartRadialCurve θ ζ ρ) hann.1
    (by linarith only [hann.2])
  have hρpos : 0 < ρ := hr.1.trans_le hρ.1
  have hζρ : 0 ≤ ζ ∧ ζ ≤ ρ / 9 := ⟨hζ.1, hζ.2.trans (by linarith only [hρ.1])⟩
  have HD := restartFastRadialPhase_derivative hhsmall hL hθ hρpos hζρ
    (mul_nonneg hA.le hr.1.le) H.2.1 H.2.2.2
  have Href := restartReferenceRadialPhase_curve_derivative hhsmall hL hθ hρpos hζρ
  have Herr : |deriv (restartFastRadialPhase h (q / 2 * Real.log (1 / r)) θ ζ) ρ -
      deriv (fun x => restartReferenceRadialPhase h (restartRadialCurve θ ζ x)) ρ| ≤ K * r := by
    calc
      _ ≤ (A * r) * (L + 1) := HD.2
      _ = K * r := by dsimp only [K]; ring
  have hKr : K * r ≤ 1 / (4 * Real.sqrt 3) := by
    have HB := (le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt 3 * K)).mp
      (hr.2.trans (min_le_right _ _))
    apply (le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt 3)).mpr
    nlinarith only [HB]
  have hlower := (abs_le.mp Herr).1
  have hupper := (abs_le.mp Herr).2
  have hquarter : 1 / (4 * Real.sqrt 3) ≤ 1 :=
    (div_le_one (by positivity : 0 < 4 * Real.sqrt 3)).mpr (by linarith only [hsqrt1])
  refine ⟨H.1, HD.1, ?_, Herr, ?_, ?_⟩
  · exact H.2.2.1.trans (mul_le_mul_of_nonneg_right hAK (sq_nonneg r))
  · have Heq : 1 / (2 * Real.sqrt 3) = 2 * (1 / (4 * Real.sqrt 3)) := by ring
    rw [Heq] at Href
    linarith only [hlower, Href.2.1, hKr]
  · linarith only [hupper, Href.2.2, hKr, hquarter]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartReferenceRadialPhase_curve_bounds {h r ρ θ ζ L : ℝ}
    (hh : 0 ≤ h ∧ h ≤ 1 / 16) (hr : 0 < r) (hρ : ρ ∈ Icc r (2 * r))
    (hL : 0 ≤ L) (hθ : |θ| ≤ L) (hζ : 0 ≤ ζ ∧ ζ ≤ r / 9) :
    r / 8 ≤ restartReferenceRadialPhase h (restartRadialCurve θ ζ ρ) ∧
      restartReferenceRadialPhase h (restartRadialCurve θ ζ ρ) ≤ 8 * (L + 1) * r := by
  let Z := restartRadialCurve θ ζ ρ
  have hnorm := (restartRadialCurve_annulus hr hρ hL hθ hζ).1
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsqrtSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := by nlinarith only [hsqrtSq, hsqrt]
  have hsqrt2 : Real.sqrt (3 : ℝ) ≤ 2 := by nlinarith only [hsqrtSq, hsqrt]
  have hv : |Z 1 - Z 2| ≤ 2 * ‖Z‖ := by
    calc
      _ ≤ |Z 1| + |Z 2| := by simpa using abs_sub_le (Z 1) 0 (Z 2)
      _ ≤ ‖Z‖ + ‖Z‖ := add_le_add (norm_le_pi_norm Z 1) (norm_le_pi_norm Z 2)
      _ = _ := by ring
  have Hupper := sqrt_restartQuadratic_le_radius hh (norm_nonneg Z) (norm_le_pi_norm Z 0) hv
  have Hlower : r / 2 ≤ Real.sqrt (restartQuadratic h (Z 0) (Z 1 - Z 2)) := by
    obtain ⟨_, _, hc, _, _, _⟩ := restart_coefficients_small hh
    have hdiff : r / 2 ≤ ρ - ζ := by linarith only [hρ.1, hζ.2, hr]
    have hcv : r / 2 ≤ restartWallFactor h * (ρ - ζ) := by
      have H := mul_le_mul_of_nonneg_right hc (by linarith only [hdiff, hr] : 0 ≤ ρ - ζ)
      nlinarith only [H, hdiff]
    have H := Real.sqrt_le_sqrt (le_add_of_nonneg_left
      (sq_nonneg (restartShearFactor h * (θ * ρ) + restartShearCoupling h * (ρ - ζ))) :
      (restartWallFactor h * (ρ - ζ)) ^ 2 ≤ restartQuadratic h (θ * ρ) (ρ - ζ))
    rw [Real.sqrt_sq (by linarith only [hcv, hr])] at H
    exact hcv.trans H
  change r / 8 ≤ Real.sqrt (restartQuadratic h (Z 0) (Z 1 - Z 2)) / Real.sqrt 3 ∧
    Real.sqrt (restartQuadratic h (Z 0) (Z 1 - Z 2)) / Real.sqrt 3 ≤ 8 * (L + 1) * r
  constructor
  · apply (le_div_iff₀ hsqrt).mpr
    have H := mul_le_mul_of_nonneg_left hsqrt2 hr.le
    linarith only [Hlower, H, hr]
  · apply (div_le_iff₀ hsqrt).mpr
    have H := mul_le_mul_of_nonneg_left hsqrt1 (show 0 ≤ 8 * (L + 1) * r by positivity)
    nlinarith only [Hupper, hnorm, H]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartProjectionPhase_state_eq (h T θ ζ ρ : ℝ) :
    restartProjectionPhase (restartSectionRadialState h T (restartRadialCurve θ ζ ρ)) =
      restartFastProjectionError h T θ ζ ρ + restartFastRadialPhase h T θ ζ ρ := by
  change restartProjectionPhase _ =
    (restartProjectionPhase _ - restartRadialPhase _) + restartRadialPhase _
  exact (sub_add_cancel _ _).symm

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_restartFastProjectionPhase_approximation :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∃ K : ℝ, 0 < K ∧ ∀ q : ℝ, 2 < q →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ r ^ 2) → ∀ ρ ∈ Icc r (2 * r),
            let T := q / 2 * Real.log (1 / r)
            let x := normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 T
            T ∈ normalizedMaxDomain (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 ∧
            0 < 1 + x 0 ∧
            DifferentiableAt ℝ (restartFastProjectionPhase h T θ ζ) ρ ∧
            |restartFastProjectionPhase h T θ ζ ρ -
              restartReferenceRadialPhase h (restartRadialCurve θ ζ ρ)| ≤ K * r ^ 2 ∧
            |deriv (restartFastProjectionPhase h T θ ζ) ρ -
              deriv (fun y => restartReferenceRadialPhase h (restartRadialCurve θ ζ y)) ρ| ≤ K * r ∧
            1 / (4 * Real.sqrt 3) ≤ deriv (restartFastProjectionPhase h T θ ζ) ρ ∧
            deriv (restartFastProjectionPhase h T θ ζ) ρ ≤ (2 * L + 3) / Real.sqrt 3 + 1 := by
  obtain ⟨hE, hhE, HE⟩ := exists_restartFastProjectionError_bounds
  obtain ⟨hR, hhR, HR⟩ := exists_restartFastRadialPhase_monotone
  refine ⟨min hE (min hR (1 / 16)), lt_min hhE (lt_min hhR (by norm_num)), ?_⟩
  intro h hh L hL
  obtain ⟨KE, hKE, HKE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL
  obtain ⟨KR, hKR, HKR⟩ := HR h ⟨hh.1, (hh.2.trans (min_le_right _ _)).trans (min_le_left _ _)⟩ L hL
  have hhsmall : 0 ≤ h ∧ h ≤ 1 / 16 :=
    ⟨hh.1.le, (hh.2.trans (min_le_right _ _)).trans (min_le_right _ _)⟩
  let K := KE + KR
  have hK : 0 < K := add_pos hKE hKR
  refine ⟨K, hK, ?_⟩
  intro q hq
  obtain ⟨rE, hrE, HrE⟩ := HKE q hq
  obtain ⟨rR, hrR, HrR⟩ := HKR q hq
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), hsqrt]
  refine ⟨min rE (min rR (min (1 / 9) (1 / (4 * Real.sqrt 3 * K)))),
    lt_min hrE (lt_min hrR (lt_min (by norm_num) (by positivity))), ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  have hrsmall : r ≤ 1 / 9 := ((hr.2.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hrK : r ≤ 1 / (4 * Real.sqrt 3 * K) :=
    ((hr.2.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hζsmall : 0 ≤ ζ ∧ ζ ≤ r / 9 := ⟨hζ.1, hζ.2.trans (by nlinarith only [hr.1, hrsmall])⟩
  let T := q / 2 * Real.log (1 / r)
  obtain ⟨Hdom, HED, HEval, HEder, Hheight, Hgerm⟩ :=
    HrE r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩ θ ζ hθ hζ ρ hρ
  obtain ⟨_, HRD, HRval, HRder, _, _⟩ :=
    HrR r ⟨hr.1, (hr.2.trans (min_le_right _ _)).trans (min_le_left _ _)⟩ θ ζ hθ hζsmall ρ hρ
  have Hlocal : restartFastProjectionPhase h T θ ζ =ᶠ[𝓝 ρ]
      (fun y => restartFastProjectionError h T θ ζ y + restartFastRadialPhase h T θ ζ y) := by
    filter_upwards [Hgerm] with y hy
    exact hy.trans (restartProjectionPhase_state_eq h T θ ζ y)
  have Hsum : HasDerivAt (restartFastProjectionPhase h T θ ζ)
      (deriv (restartFastProjectionError h T θ ζ) ρ + deriv (restartFastRadialPhase h T θ ζ) ρ) ρ := by
    convert! (HED.hasDerivAt.add HRD.hasDerivAt).congr_of_eventuallyEq Hlocal using 1
  have Hval : |restartFastProjectionPhase h T θ ζ ρ -
      restartReferenceRadialPhase h (restartRadialCurve θ ζ ρ)| ≤ K * r ^ 2 := by
    rw [Hlocal.eq_of_nhds, add_sub_assoc]
    calc
      _ ≤ |restartFastProjectionError h T θ ζ ρ| +
          |restartFastRadialPhase h T θ ζ ρ - restartReferenceRadialPhase h (restartRadialCurve θ ζ ρ)| := abs_add_le _ _
      _ ≤ KE * r ^ 2 + KR * r ^ 2 := add_le_add HEval HRval
      _ = K * r ^ 2 := by dsimp only [K]; ring
  have Hder : |deriv (restartFastProjectionPhase h T θ ζ) ρ -
      deriv (fun y => restartReferenceRadialPhase h (restartRadialCurve θ ζ y)) ρ| ≤ K * r := by
    rw [Hsum.deriv, add_sub_assoc]
    calc
      _ ≤ |deriv (restartFastProjectionError h T θ ζ) ρ| +
          |deriv (restartFastRadialPhase h T θ ζ) ρ -
            deriv (fun y => restartReferenceRadialPhase h (restartRadialCurve θ ζ y)) ρ| := abs_add_le _ _
      _ ≤ KE * r + KR * r := add_le_add HEder HRder
      _ = K * r := by dsimp only [K]; ring
  have Href := restartReferenceRadialPhase_curve_derivative hhsmall hL hθ (hr.1.trans_le hρ.1)
    ⟨hζ.1, hζsmall.2.trans (by linarith only [hρ.1])⟩
  have hKr : K * r ≤ 1 / (4 * Real.sqrt 3) := by
    have H := (le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt 3 * K)).mp hrK
    apply (le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt 3)).mpr
    nlinarith only [H]
  have hquarter : 1 / (4 * Real.sqrt 3) ≤ 1 :=
    (div_le_one (by positivity : 0 < 4 * Real.sqrt 3)).mpr (by linarith only [hsqrt1])
  refine ⟨Hdom, Hheight, Hsum.differentiableAt, Hval, Hder, ?_, ?_⟩
  · have heq : 1 / (2 * Real.sqrt 3) = 2 * (1 / (4 * Real.sqrt 3)) := by ring
    rw [heq] at Href
    linarith only [(abs_le.mp Hder).1, Href.2.1, hKr]
  · linarith only [(abs_le.mp Hder).2, Href.2.2, hKr, hquarter]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartFastCoreRadius_eq_reciprocal (h T θ ζ ρ : ℝ) :
    restartFastCoreRadius h T θ ζ ρ = 2 / restartFastProjectionPhase h T θ ζ ρ := by
  simp [restartFastCoreRadius, restartFastProjectionPhase]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartFastCoreRadius_bounds :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∀ q : ℝ, 2 < q →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ r ^ 2) → ∀ ρ ∈ Icc r (2 * r),
            let T := q / 2 * Real.log (1 / r)
            let B := 8 * (L + 1) + 1
            T ∈ normalizedMaxDomain (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 ∧
            DifferentiableAt ℝ (restartFastCoreRadius h T θ ζ) ρ ∧
            6 ≤ restartFastCoreRadius h T θ ζ ρ ∧
            2 / (B * r) ≤ restartFastCoreRadius h T θ ζ ρ ∧
            restartFastCoreRadius h T θ ζ ρ ≤ 32 / r ∧
            1 / (4 * B ^ 2 * r ^ 2) ≤ -deriv (restartFastCoreRadius h T θ ζ) ρ ∧
            -deriv (restartFastCoreRadius h T θ ζ) ρ ≤ 512 * (2 * L + 4) / r ^ 2 := by
  obtain ⟨hstar, hhstar, HH⟩ := exists_restartFastProjectionPhase_approximation
  refine ⟨min hstar (1 / 16), lt_min hhstar (by norm_num), ?_⟩
  intro h hh L hL q hq
  obtain ⟨K, hK, HK⟩ := HH h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL
  obtain ⟨rA, hrA, HA⟩ := HK q hq
  let B := 8 * (L + 1) + 1
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨min rA (min (1 / 9) (min (1 / (16 * K)) (1 / (3 * B)))),
    lt_min hrA (lt_min (by norm_num) (lt_min (by positivity) (by positivity))), ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  have hr9 : r ≤ 1 / 9 := (hr.2.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hrK : r ≤ 1 / (16 * K) :=
    ((hr.2.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hrB : r ≤ 1 / (3 * B) :=
    ((hr.2.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hKr : K * r ≤ 1 / 16 := by
    have H := (le_div_iff₀ (by positivity : 0 < 16 * K)).mp hrK
    linarith only [H]
  have herr : K * r ^ 2 ≤ r / 16 := by
    nlinarith only [mul_le_mul_of_nonneg_right hKr hr.1.le]
  let T := q / 2 * Real.log (1 / r)
  obtain ⟨Hdom, _, HD, Hval, _, Hdl, Hdu⟩ :=
    HA r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩ θ ζ hθ hζ ρ hρ
  obtain ⟨Hreflo, Hrefhi⟩ := restartReferenceRadialPhase_curve_bounds
    ⟨hh.1.le, hh.2.trans (min_le_right _ _)⟩ hr.1 hρ hL hθ
    ⟨hζ.1, hζ.2.trans (by nlinarith only [hr.1, hr9])⟩
  have Hlo : r / 16 ≤ restartFastProjectionPhase h T θ ζ ρ := by
    linarith only [(abs_le.mp Hval).1, Hreflo, herr]
  have Hhi : restartFastProjectionPhase h T θ ζ ρ ≤ B * r := by
    dsimp only [B]
    nlinarith only [(abs_le.mp Hval).2, Hrefhi, herr, hr.1]
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsqrtSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := by nlinarith only [hsqrtSq, hsqrt]
  have hsqrt2 : Real.sqrt (3 : ℝ) ≤ 2 := by nlinarith only [hsqrtSq, hsqrt]
  have Hdlo : 1 / 8 ≤ deriv (restartFastProjectionPhase h T θ ζ) ρ := by
    apply le_trans _ Hdl
    apply (le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt 3)).mpr
    linarith only [hsqrt2]
  have Hdhi : deriv (restartFastProjectionPhase h T θ ζ) ρ ≤ 2 * L + 4 := by
    have H : (2 * L + 3) / Real.sqrt 3 ≤ 2 * L + 3 := by
      apply (div_le_iff₀ hsqrt).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hsqrt1 (by positivity : 0 ≤ 2 * L + 3)]
    linarith only [Hdu, H]
  obtain ⟨HKD, HKlo, HKhi, HKdlo, HKdhi⟩ :=
    reciprocal_radial_bounds hr.1 (show 0 ≤ 2 * L + 4 by positivity) HD Hlo Hhi Hdlo Hdhi
  have Heq : restartFastCoreRadius h T θ ζ = fun y => 2 / restartFastProjectionPhase h T θ ζ y :=
    funext (restartFastCoreRadius_eq_reciprocal h T θ ζ)
  have Hsix : 6 ≤ 2 / (B * r) := by
    apply (le_div_iff₀ (mul_pos hB hr.1)).mpr
    have H := (le_div_iff₀ (by positivity : 0 < 3 * B)).mp hrB
    nlinarith only [H]
  change _ ∧ DifferentiableAt ℝ (restartFastCoreRadius h T θ ζ) ρ ∧ _
  rw [Heq]
  exact ⟨Hdom, HKD, Hsix.trans HKlo, HKlo, HKhi, HKdlo, HKdhi⟩

end
end

/-- E.13 holds at the reflected endpoint of the same original Einstein orbit. -/
theorem solution :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∀ q P : ℝ, 3 < q → 4 < P →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ r ^ P) → ∀ ρ ∈ Icc r (2 * r),
            let s := q / 2 * Real.log (1 / r)
            let y := restartFastProjectiveEntry h s θ ζ ρ
            let x := restartSectionChart h (restartRadialCurve θ ζ ρ)
            let M := 8 * (L + 1)
            let B := M + 1
            ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow y 0 t 2 = 1} T ∧
              let p := coreExitConnectionParameters (toCoreAngleState (projectiveOriginalFlow y 0 T))
              let G := connectionReturnPhysicalState p
              connectionReturnValid p ∧
              1 / (2 * B * r) ≤ G 0 ∧ G 0 ≤ 64 / r ∧
              0 < G 1 ∧ 0 < G 2 ∧ G 1 + G 2 ≤ 4096 * M * ζ / r ^ 3 ∧
              coreRadiusEntry G = projectiveReflection (toProjectiveState
                (normalizedMaxCurve x 0 (s + T + connectionReturnTime p))) := by
  obtain ⟨hE, hhE, HE⟩ := exists_restartPartialCore_connection
  obtain ⟨hV, hhV, HV⟩ := exists_restartFastProjectiveEntry_bounds
  obtain ⟨hR, hhR, HR⟩ := exists_restartFastCoreRadius_bounds
  refine ⟨min hE (min hV hR), lt_min hhE (lt_min hhV hhR), ?_⟩
  intro h hh L hL q P hq hP
  have hq2 : 2 < q := by linarith only [hq]
  obtain ⟨rE, hrE, HRE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL q P hq hP
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  obtain ⟨rV, hrV, HRV⟩ := HV h ⟨hh.1, (hh.2.trans (min_le_right _ _)).trans (min_le_left _ _)⟩ L hL q hq2
  obtain ⟨rR, hrR, HRR⟩ := HR h ⟨hh.1, (hh.2.trans (min_le_right _ _)).trans (min_le_right _ _)⟩ L hL q hq2
  refine ⟨min rE (min rV (min rR 1)), lt_min hrE (lt_min hrV (lt_min hrR (by norm_num))), ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  have hrV' := hr.2.trans (min_le_right _ _)
  have hrR' := hrV'.trans (min_le_right _ _)
  have hr1 := hrR'.trans (min_le_right _ _)
  have hζ2 : 0 ≤ ζ ∧ ζ ≤ r ^ 2 := by
    refine ⟨hζ.1.le, hζ.2.trans ?_⟩
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge hr.1 hr1 (by linarith only [hP] : (2 : ℝ) ≤ P)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hprod, _⟩ :=
    HRV r ⟨hr.1, hrV'.trans (min_le_left _ _)⟩ θ ζ hθ hζ2 ρ hρ
  obtain ⟨_, _, _, hklo, hkhi, _⟩ := HRR r ⟨hr.1, hrR'.trans (min_le_left _ _)⟩ θ ζ hθ hζ2 ρ hρ
  obtain ⟨T, hT, hfirst, _, _, hμ, hu, hw, _, hweak, _, hvalid, _, _, horbit⟩ :=
    HRE r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩ θ ζ hθ hζ ρ hρ
  let s := q / 2 * Real.log (1 / r)
  let y := restartFastProjectiveEntry h s θ ζ ρ
  let p := coreExitConnectionParameters (toCoreAngleState (projectiveOriginalFlow y 0 T))
  let G := connectionReturnPhysicalState p
  let M := 8 * (L + 1)
  let B := M + 1
  obtain ⟨Hlo, Hhi, Hstrong, Hweak, Hsum, Hentry⟩ := connectionReturn_restart_bounds hμ.1 hu hw
  have Hlower : 1 / (2 * B * r) ≤ G 0 := by
    have H := hμ.2.1
    have Heq : 2 / ((8 * (L + 1) + 1) * r) = 4 * (1 / (2 * B * r)) := by dsimp only [B, M]; field_simp; norm_num
    rw [Heq] at hklo
    linarith only [hklo, H, Hlo]
  have Hupper : G 0 ≤ 64 / r := by
    have H := hμ.2.2.le.trans hkhi
    exact Hhi.trans ((mul_le_mul_of_nonneg_left H (by norm_num)).trans_eq (by ring))
  refine ⟨T, hT, hfirst, hvalid, Hlower, Hupper, Hstrong.1, Hweak.1, ?_, ?_⟩
  · exact Hsum.trans ((mul_le_mul_of_nonneg_left (hweak.trans hprod.2) (by norm_num)).trans_eq (by ring))
  · rw [horbit] at Hentry
    exact Hentry
