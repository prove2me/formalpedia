-- Prove2me | solution 1 for BianchiIX.exists_terminal_single_phase_composed_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T23:24:40.413198+00:00
-- url     : https://prove2.me/submissions/75e36a69-bdfd-4b6c-95f8-41ad2f47b38f

import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_TerminalConeData
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Theorems.Thm_BianchiIX_coreTailValid_of_height_le
import Theorems.Thm_BianchiIX_exists_terminal_axisCycle_regular
import Theorems.Thm_BianchiIX_exists_terminal_exitReturn_radial_bounds_uniform
import Theorems.Thm_BianchiIX_exitSingleError_scalar_bounds
import Theorems.Thm_BianchiIX_exitSinglePhase_derivative_bounds
import Theorems.Thm_BianchiIX_exitSingle_terminal_geometry
import Theorems.Thm_BianchiIX_terminalSinglePhase_eventuallyEq_radical
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
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
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
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
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
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Order.ProjIcc
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp

noncomputable section
open BianchiIX
open Filter
open scoped Topology

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailLength_nonneg {η α : ℝ} (hη : 0 < η ∧ η ≤ 1) (hα : 0 < α ∧ α ≤ 1) (J : ℕ) :
    0 ≤ exitTailLength η α J := by
  have he : 0 ≤ Real.log (1 / η) := Real.log_nonneg ((le_div_iff₀ hη.1).mpr (by linarith only [hη.2]))
  have ha : 0 ≤ Real.log (1 / α) := Real.log_nonneg ((le_div_iff₀ hα.1).mpr (by linarith only [hα.2]))
  exact add_nonneg he (mul_nonneg (Nat.cast_nonneg _) ha)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.power_mul_log_inv_bound {α : ℝ} (hα : 0 < α) (J : ℕ) :
    α ^ J * ((J : ℝ) * Real.log (1 / α)) ≤ Real.exp (-1) := by
  have H := Real.mul_exp_neg_le_exp_neg_one ((J : ℝ) * Real.log (1 / α))
  have he : Real.exp (-((J : ℝ) * Real.log (1 / α))) = α ^ J := by
    rw [one_div, Real.log_inv, mul_neg, neg_neg, Real.exp_nat_mul, Real.exp_log hα]
  rw [he] at H
  linarith only [H]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.sq_mul_exp_neg_bound {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 * Real.exp (-x) ≤ 4 * Real.exp (-2) := by
  have H := Real.mul_exp_neg_le_exp_neg_one (x / 2)
  have hpos : 0 ≤ x / 2 * Real.exp (-(x / 2)) := mul_nonneg (by positivity) (Real.exp_pos _).le
  have Hsq := (sq_le_sq₀ hpos (Real.exp_pos _).le).mpr H
  have h1 : Real.exp (-(x / 2)) ^ 2 = Real.exp (-x) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp (-1) ^ 2 = Real.exp (-2) := by rw [sq, ← Real.exp_add]; norm_num
  rw [mul_pow, h1, h2] at Hsq
  nlinarith only [Hsq]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailLength_weighted_bounds {η α : ℝ} (hη : 0 < η ∧ η ≤ 1)
    (hα : 0 < α ∧ α ≤ 1) (J : ℕ) :
    α * exitTailLength η α J ≤ Real.log (1 / η) + J * Real.exp (-1) ∧
    α ^ J * (1 + exitTailLength η α J) ≤ 1 + Real.log (1 / η) + Real.exp (-1) ∧
    α ^ J * (1 + exitTailLength η α J) ^ 2 ≤
      2 * (1 + Real.log (1 / η)) ^ 2 + 8 * Real.exp (-2) := by
  have he : 0 ≤ Real.log (1 / η) := Real.log_nonneg ((le_div_iff₀ hη.1).mpr (by linarith only [hη.2]))
  have ha : 0 ≤ Real.log (1 / α) := Real.log_nonneg ((le_div_iff₀ hα.1).mpr (by linarith only [hα.2]))
  have hp0 := pow_nonneg hα.1.le J
  have hp1 : α ^ J ≤ 1 := pow_le_one₀ hα.1.le hα.2
  have H1 := power_mul_log_inv_bound hα.1 1
  simp only [pow_one, Nat.cast_one, one_mul] at H1
  have HJ := power_mul_log_inv_bound hα.1 J
  have Hsq := sq_mul_exp_neg_bound (mul_nonneg (Nat.cast_nonneg J) ha)
  have hExp : Real.exp (-((J : ℝ) * Real.log (1 / α))) = α ^ J := by
    rw [one_div, Real.log_inv, mul_neg, neg_neg, Real.exp_nat_mul, Real.exp_log hα.1]
  rw [hExp] at Hsq
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [exitTailLength]
    nlinarith only [mul_le_mul_of_nonneg_right hα.2 he,
      mul_le_mul_of_nonneg_left H1 (Nat.cast_nonneg J)]
  · dsimp only [exitTailLength]
    nlinarith only [HJ, mul_le_mul_of_nonneg_right hp1 (by positivity : 0 ≤ 1 + Real.log (1 / η))]
  · have Hsplit : (1 + exitTailLength η α J) ^ 2 ≤
        2 * (1 + Real.log (1 / η)) ^ 2 + 2 * ((J : ℝ) * Real.log (1 / α)) ^ 2 := by
      dsimp only [exitTailLength]
      nlinarith only [sq_nonneg (1 + Real.log (1 / η) - J * Real.log (1 / α))]
    have H := mul_le_mul_of_nonneg_left Hsplit hp0
    have HB := mul_le_mul_of_nonneg_right hp1 (sq_nonneg (1 + Real.log (1 / η)))
    nlinarith only [H, HB, Hsq]

end
end

section
noncomputable section
open BianchiIX
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem BianchiIX.clm_norm_le_card_mul_basis_bound {n : ℕ} (L : (Fin n → ℝ) →L[ℝ] F)
    {C : ℝ} (hC : 0 ≤ C) (hL : ∀ i, ‖L (Pi.single i 1)‖ ≤ C) : ‖L‖ ≤ n * C := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hv : (∑ i : Fin n, v i • (Pi.single i 1 : Fin n → ℝ)) = v := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have HL : L v = ∑ i : Fin n, v i • L (Pi.single i 1) := by
    rw [← hv, map_sum]
    simp only [map_smul, hv]
  calc
    ‖L v‖ = ‖∑ i : Fin n, v i • L (Pi.single i 1)‖ := congrArg norm HL
    _ ≤ ∑ i : Fin n, ‖v i • L (Pi.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, ‖v‖ * C := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul (norm_le_pi_norm v i) (hL i) (norm_nonneg _) (norm_nonneg v)
    _ = (n : ℝ) * C * ‖v‖ := by simp; ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailGap_sq {R v : ℝ} (h : v ^ 2 ≤ R ^ 2) :
    exitTailGap R v ^ 2 = R ^ 2 - v ^ 2 := Real.sq_sqrt (sub_nonneg.mpr h)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailGap_terminal_offset {α B R v : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hB : B ≤ α / 10000) (hR : |R - (2 + 2 * α)| ≤ B) (hv : 0 ≤ v ∧ v ≤ α / 100) :
    199 / 100 * α < exitTailGap R v - 2 ∧ exitTailGap R v - 2 < 201 / 100 * α := by
  have hα0 : 0 < α := hα.1
  have hRc := abs_le.mp hR
  have hRlo : 2 + 19999 / 10000 * α ≤ R := by linarith only [hRc.1, hB]
  have hR0 : 0 ≤ R := by linarith only [hRlo, hα.1]
  have hRsq := (sq_le_sq₀ (by positivity) hR0).mpr hRlo
  have hvsq := (sq_le_sq₀ hv.1 (by positivity)).mpr hv.2
  have hvR : v ^ 2 ≤ R ^ 2 := by nlinarith only [hRsq, hvsq, hα.1, sq_nonneg α]
  have ht := exitTailGap_sq hvR
  have ht0 : 0 ≤ exitTailGap R v := Real.sqrt_nonneg _
  have hs : (2 + 199 / 100 * α) ^ 2 < (exitTailGap R v) ^ 2 := by
    nlinarith only [hRsq, hvsq, ht, hα.1, sq_nonneg α]
  have hlo := (sq_lt_sq₀ (by positivity) ht0).mp hs
  have hhi : exitTailGap R v ≤ R := (Real.sqrt_le_left hR0).mpr (by nlinarith only [sq_nonneg v])
  constructor <;> linarith only [hlo, hhi, hRc.2, hB, hα.1]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitSingleSquare_eq {R v : ℝ} (hH : exitSingleBase R v ≠ 0) (u w : ℝ) :
    R ^ 2 + exitSingleError R u v w =
      4 + (exitSingleBase R v + exitSingleDefect u v w) *
        (R ^ 2 - 4 + exitSingleDefect u v w) / exitSingleBase R v := by
  dsimp only [exitSingleError]
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitSingleDefect_bound {b u v w : ℝ} (hv : 0 ≤ v) (hw : |u| + |w| ≤ b) :
    |exitSingleDefect u v w| ≤ 2 * b * (v + b) := by
  have hb : 0 ≤ b := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans hw
  have Hsub : |u - w| ≤ b := (abs_sub u w).trans hw
  have Hadd : |u + w| ≤ b := (abs_add_le u w).trans hw
  calc
    |exitSingleDefect u v w| ≤ |(u - w) ^ 2| + |2 * v * (u + w)| := abs_sub _ _
    _ = |u - w| ^ 2 + 2 * v * |u + w| := by
      rw [abs_pow, abs_mul, abs_mul, abs_of_nonneg hv]; norm_num
    _ ≤ b ^ 2 + 2 * v * b := by gcongr
    _ ≤ 2 * b * (v + b) := by nlinarith only [sq_nonneg b]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitSingle_terminal_error_bounds {α b R u v w : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hb : b ≤ α / 10000) (hR : |R - (2 + 2 * α)| ≤ α / 10000)
    (hw : |u| + |w| ≤ b) (hv : 0 ≤ v ∧ v ≤ α / 100) :
    2 < Real.sqrt (R ^ 2 + exitSingleError R u v w) ∧
      |exitSingleError R u v w| ≤ 46 * b * (v + b) / α ∧
      |exitSingleErrorRadial R u v w| ≤ 900 * b * (v + b) / α ^ 2 ∧
      |exitSingleErrorWallFactor R u v w| ≤ 24 / α := by
  have hα0 := hα.1
  obtain ⟨HR, HRhi, HG, HGhi, Hsq, HH, HT, HN, HHpos, HNpos⟩ :=
    exitSingle_terminal_geometry hα hb hR hw hv
  have HH₀ : 0 < exitSingleBase R v := lt_of_lt_of_le (sq_pos_of_pos hα0) HH
  have HG0 : 0 < exitTailGap R v := lt_trans (by norm_num) HG
  have HR0 : 0 ≤ R := by linarith only [HR]
  have Hoffset := exitTailGap_terminal_offset hα (le_refl (α / 10000)) hR hv
  have HGdiff : exitTailGap R v - 2 ≤ 3 * α := by linarith only [Hoffset.2, hα.1]
  have HL : |exitSingleBaseRadial R v| ≤ 20 * α := by
    rw [exitSingleBaseRadial, abs_of_nonneg (by positivity)]
    calc
      _ ≤ 2 * (3 * α) * 5 / 2 := by gcongr
      _ ≤ _ := by linarith only [hα.1]
  have HE := exitSingleError_scalar_bounds hα ⟨HR0, HRhi⟩ HH HT HN HL
    (exitSingleDefect_bound hv.1 hw)
  have HS : 4 < R ^ 2 + exitSingleError R u v w := by
    rw [exitSingleSquare_eq HH₀.ne']
    linarith only [div_pos (mul_pos HHpos HNpos) HH₀]
  refine ⟨(Real.lt_sqrt (by norm_num)).mpr (by norm_num; exact HS), ?_, ?_, HE.2.2.2⟩
  · have H := HE.1
    change |exitSingleError R u v w| ≤ 23 * (2 * b * (v + b)) / α at H
    convert H using 1; ring
  · have H := HE.2.2.1
    change |exitSingleErrorRadial R u v w| ≤ 450 * (2 * b * (v + b)) / α ^ 2 at H
    convert H using 1; ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.coreTailState_active {η : ℝ} {Y : CoreAngleState} (hvalid : coreTailValid η Y) :
    coreTailState η Y 2 = η := hvalid.1.1.2.2

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_terminal_tail_geometry_uniform {η₀ : ℝ} (hη₀ : 0 < η₀ ∧ η₀ ≤ 1 / 100)
    {J : ℕ} (hJ : 1 ≤ J) :
    ∃ A ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ 1 / 100 → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let y := coreTailState h Y
      coreTailValid h Y ∧ y 0 < 1 ∧
        |coreRadius (y 0) (y 2) - (2 + 2 * α)| ≤ A * b ∧
        |y 1| + |y 3| ≤ A * b ∧ A * b ≤ α / 10000 ∧
        (0 ≤ y 2 ∧ y 2 ≤ α / 100) ∧ 39 / 10 * α ^ 2 ≤ projectiveCycleDenom y := by
  obtain ⟨A, hA, ε, hε, HE⟩ := exists_terminal_axisCycle_regular hη₀ hJ
  refine ⟨A, hA, ε, hε, ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum Y h y
  have hη : 0 < η := hη₀.1.trans_le hηlo
  obtain ⟨HV₀, HB, HF, _⟩ := HE α b u w hα hb hsmall hsum
  have hh1 : h < 1 := by
    have H := mul_le_mul_of_nonneg_left (pow_le_one₀ hα.1.le hα.2 (n := J)) hη.le
    dsimp only [h]
    nlinarith only [H, hηhi]
  obtain ⟨HV, htime⟩ := coreTailValid_of_height_le HV₀
    (mul_le_mul_of_nonneg_right hηlo (pow_nonneg hα.1.le J)) hh1
  change coreTailValid h Y at HV
  have H := HF (coreTailTime h Y) ⟨HV.1.1.1.le, htime⟩
  have HB' : A * b ≤ α / 10000 := HB.trans (div_le_div_of_nonneg_right
    ((pow_le_pow_of_le_one hα.1.le hα.2 (by omega : 1 ≤ 2 * J)).trans_eq (pow_one α)) (by norm_num))
  have hv : 0 ≤ y 2 ∧ y 2 ≤ α / 100 := by
    change 0 ≤ coreTailState h Y 2 ∧ coreTailState h Y 2 ≤ _
    rw [coreTailState_active HV]
    refine ⟨mul_nonneg hη.le (pow_nonneg hα.1.le J), ?_⟩
    have hp := (pow_le_pow_of_le_one hα.1.le hα.2 hJ).trans_eq (pow_one α)
    change η * α ^ J ≤ _
    nlinarith only [mul_le_mul_of_nonneg_left hp hη.le, mul_le_mul_of_nonneg_right hηhi hα.1.le]
  refine ⟨HV, H.1, H.2.1, H.2.2.1, HB', hv, ?_⟩
  have HH : 39 / 10 * α ^ 2 + 2 / 5 * (y 2) ^ 2 < projectiveCycleDenom y := H.2.2.2.1
  nlinarith only [HH, sq_nonneg (y 2)]

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.exitSinglePhase_value_bound {α b R u v w : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hb : b ≤ α / 10000) (hR : |R - (2 + 2 * α)| ≤ α / 10000)
    (hw : |u| + |w| ≤ b) (hv : 0 ≤ v ∧ v ≤ α / 100) :
    |exitSinglePhase R u v w - (R - 2) / 2| ≤ 23 * b * (v + b) / α := by
  have HR := (exitSingle_terminal_geometry hα hb hR hw hv).1
  obtain ⟨HX, HE, _, _⟩ := exitSingle_terminal_error_bounds hα hb hR hw hv
  let X := Real.sqrt (R ^ 2 + exitSingleError R u v w)
  change 2 < X at HX
  have HS : X ^ 2 = R ^ 2 + exitSingleError R u v w :=
    Real.sq_sqrt (Real.sqrt_pos.mp (by linarith only [HX] : 0 < X)).le
  have HD : |X - R| ≤ |exitSingleError R u v w| := by
    have H := congrArg abs (show (X - R) * (X + R) = exitSingleError R u v w by nlinarith only [HS])
    rw [abs_mul, abs_of_pos (by linarith only [HR, HX] : 0 < X + R)] at H
    nlinarith only [H, HR, HX, abs_nonneg (X - R)]
  have Hid : exitSinglePhase R u v w - (R - 2) / 2 = (X - R) / 2 := by
    dsimp only [exitSinglePhase, X]; ring
  rw [Hid, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact (div_le_div_of_nonneg_right (HD.trans HE) (by norm_num)).trans_eq (by ring)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.clm_three_coordinate_bound (L : ExitTailState →L[ℝ] ℝ) (v : ExitTailState) :
    |L v| ≤ |v 0| * |L (Pi.single 0 1)| + |v 1| * |L (Pi.single 1 1)| + |v 2| * |L (Pi.single 2 1)| := by
  have hv : v = v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 + v 2 • Pi.single 2 1 := by
    ext j
    fin_cases j <;> simp
  conv_lhs => rw [hv, map_add, map_add, map_smul, map_smul, map_smul]
  simpa only [smul_eq_mul, abs_mul] using
    (abs_add_le (v 0 * L (Pi.single 0 1) + v 1 * L (Pi.single 1 1))
      (v 2 * L (Pi.single 2 1))).trans (add_le_add (abs_add_le _ _) le_rfl)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.clm_three_radial_composition_bound (P : ExitTailState →L[ℝ] ℝ) (d : ExitTailState) :
    |P d - 1 / 2| ≤ |P (Pi.single 0 1) - 1 / 2| * |d 0| + |d 0 - 1| / 2 +
      (|P (Pi.single 1 1)| + |P (Pi.single 2 1)|) * (|d 1| + |d 2|) := by
  let Q : ExitTailState →L[ℝ] ℝ := P - (1 / 2 : ℝ) • ContinuousLinearMap.proj 0
  have H := clm_three_coordinate_bound Q d
  have H0 : Q (Pi.single 0 1) = P (Pi.single 0 1) - 1 / 2 := by simp [Q]
  have H1 : Q (Pi.single 1 1) = P (Pi.single 1 1) := by simp [Q]
  have H2 : Q (Pi.single 2 1) = P (Pi.single 2 1) := by simp [Q]
  rw [H0, H1, H2] at H
  have Heq : P d - 1 / 2 = Q d + (d 0 - 1) / 2 := by
    simp only [Q, sub_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    ring
  rw [Heq]
  have Hsum := abs_add_le (Q d) ((d 0 - 1) / 2)
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at Hsum
  nlinarith only [H, Hsum, mul_nonneg (abs_nonneg (P (Pi.single 1 1))) (abs_nonneg (d 2)),
    mul_nonneg (abs_nonneg (P (Pi.single 2 1))) (abs_nonneg (d 1))]

end
end


/-- The actual finite-tail single-wall phase has O(b) value and radial errors, and bounded ordinary wall columns. -/
theorem solution {η₀ : ℝ} (hη₀ : 0 < η₀ ∧ η₀ ≤ 1 / 100)
    {J : ℕ} (hJ : 2 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ 1 / 100 → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalSinglePhase h) Y ∧
        (|terminalSinglePhase h Y - α| + |fderiv ℝ (terminalSinglePhase h) Y (Pi.single 0 1) - 1 / 2| ≤ C * b) ∧
        ‖fderiv ℝ (terminalSinglePhase h) Y‖ ≤ C := by
  have hJ1 : 1 ≤ J := by omega
  obtain ⟨A, hA, εt, hεt, HT⟩ := exists_terminal_exitReturn_radial_bounds_uniform
    ⟨hη₀.1, hη₀.2.trans_lt (by norm_num)⟩ hJ1
  obtain ⟨B, hB, εg, hεg, HG⟩ := exists_terminal_tail_geometry_uniform hη₀ hJ1
  have hA0 : 0 ≤ A := (by norm_num : (0 : ℝ) ≤ 1).trans hA
  have hB0 : 0 ≤ B := (by norm_num : (0 : ℝ) ≤ 1).trans hB
  let L := 1 + Real.log (1 / η₀) + J * Real.exp (-1)
  have hL : 0 ≤ L := by
    have Hlog : 0 ≤ Real.log (1 / η₀) := Real.log_nonneg ((le_div_iff₀ hη₀.1).mpr (by linarith only [hη₀.2]))
    dsimp only [L]; positivity
  let P := 1024 * B * (1 + B)
  let W := 1024 * (1 + B)
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  let V := P + B
  let R := A * (P + W + 1 + L ^ 2)
  let N := 3 * A * (P + W + 1)
  let C := V + R + N + 1
  have hV : 0 ≤ V := add_nonneg hP hB0
  have hRad : 0 ≤ R := by dsimp only [R]; positivity
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  refine ⟨C, by dsimp only [C]; linarith only [hV, hRad, hN],
    min εt (min εg 1), lt_min hεt (lt_min hεg (by norm_num)), ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum Y h
  have hα0 := hα.1
  have hη : 0 < η := hη₀.1.trans_le hηlo
  have hst : b ≤ εt * α ^ J := hsmall.trans
    ((mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hα.1.le _)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hα.1.le hα.2 (by omega)) hεt.le))
  have hsg := hsmall.trans (mul_le_mul_of_nonneg_right
    ((min_le_right _ _).trans (min_le_left _ _)) (pow_nonneg hα.1.le (2 * J)))
  have hε1 : min εt (min εg 1) ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hbα : b ≤ α ^ 2 := hsmall.trans ((mul_le_of_le_one_left (pow_nonneg hα.1.le _) hε1).trans
    (pow_le_pow_of_le_one hα.1.le hα.2 (by omega : 2 ≤ 2 * J)))
  have hb1 : b ≤ 1 := hbα.trans (pow_le_one₀ hα.1.le hα.2)
  have hhα : h ≤ α ^ 2 := (mul_le_of_le_one_left (pow_nonneg hα.1.le J) (hηhi.trans (by norm_num))).trans
    (pow_le_pow_of_le_one hα.1.le hα.2 hJ)
  obtain ⟨HV, Hreg, Hnorm, Hrad, Hwall⟩ := HT η α b u w hηlo (hηhi.trans_lt (by norm_num)) hα hb hst hsum
  obtain ⟨_, hm, Hr, Hβ, HBsmall, Hv, _⟩ := HG η α b u w hηlo hηhi hα hb hsg hsum
  let F := fun Z => toExitTailState (coreTailState h Z)
  let z := F Y
  let β := |z 1| + |z 2|
  let f := fun Q : ExitTailState => exitSinglePhase (Q 0) (Q 1) h (Q 2)
  change ContDiffAt ℝ 2 F Y at Hreg
  change ‖fderiv ℝ F Y‖ ≤ A at Hnorm
  change |z 0 - (2 + 2 * α)| ≤ B * b at Hr
  change β ≤ B * b at Hβ
  have hβ : 0 ≤ β := by dsimp only [β]; positivity
  have Hactive : coreTailState h Y 2 = h := coreTailState_active HV
  rw [Hactive] at Hv
  have hβsmall : β ≤ α / 10000 := Hβ.trans HBsmall
  have hrsmall := Hr.trans HBsmall
  have Hfg := exitSinglePhase_derivative_bounds hα hβsmall hrsmall (le_refl β) Hv
  change ContDiffAt ℝ 2 f z ∧ _ at Hfg
  obtain ⟨_, _, _, _, Hsq, HH, _, _, HHpos, HNpos⟩ :=
    exitSingle_terminal_geometry hα hβsmall hrsmall (le_refl β) Hv
  have Hnear := terminalSinglePhase_eventuallyEq_radical
    (by change 1 < 2 + 2 * α; linarith only [hα.1]) HV hm Hreg.continuousAt Hsq
    ((sq_pos_of_pos hα.1).trans_le HH) HHpos HNpos
  change terminalSinglePhase h =ᶠ[𝓝 Y] f ∘ F at Hnear
  have Hsmooth : ContDiffAt ℝ 2 (terminalSinglePhase h) Y := (Hfg.1.comp Y Hreg).congr_of_eventuallyEq Hnear
  have Hder : fderiv ℝ (terminalSinglePhase h) Y = (fderiv ℝ f z).comp (fderiv ℝ F Y) :=
    Hnear.fderiv_eq.trans (fderiv_comp Y (Hfg.1.differentiableAt (by norm_num)) (Hreg.differentiableAt (by norm_num)))
  have Hsum : h + β ≤ (1 + B) * α ^ 2 := by
    nlinarith only [hhα, Hβ.trans (mul_le_mul_of_nonneg_left hbα hB0)]
  have Hf0 : |fderiv ℝ f z (Pi.single 0 1) - 1 / 2| ≤ P * b := Hfg.2.1.trans (by
    apply (div_le_iff₀ (sq_pos_of_pos hα.1)).mpr
    have H := mul_le_mul Hβ Hsum (by positivity : 0 ≤ h + β) (mul_nonneg hB0 hb.le)
    dsimp only [P]
    nlinarith only [H])
  have Hfw : |fderiv ℝ f z (Pi.single 1 1)| + |fderiv ℝ f z (Pi.single 2 1)| ≤ W * α := Hfg.2.2.trans (by
    apply (div_le_iff₀ hα.1).mpr
    dsimp only [W]
    nlinarith only [Hsum])
  have Hvalue : |terminalSinglePhase h Y - α| ≤ V * b := by
    have HE := exitSinglePhase_value_bound hα hβsmall hrsmall (le_refl β) Hv
    have Heq : terminalSinglePhase h Y = f z := Hnear.self_of_nhds
    rw [Heq]
    have HE' : |f z - (z 0 - 2) / 2| ≤ P * b := HE.trans (by
      apply (div_le_iff₀ hα.1).mpr
      have H := mul_le_mul Hβ Hsum (by positivity : 0 ≤ h + β) (mul_nonneg hB0 hb.le)
      have Hα := mul_le_mul_of_nonneg_left hα.2 (by positivity : 0 ≤ B * (1 + B) * b * α)
      dsimp only [P]
      nlinarith only [H, Hα, (by positivity : 0 ≤ B * (1 + B) * b * α)])
    have Hcenter : |(z 0 - 2) / 2 - α| ≤ B * b / 2 := by
      have HEQ : (z 0 - 2) / 2 - α = (z 0 - (2 + 2 * α)) / 2 := by ring
      rw [HEQ, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact div_le_div_of_nonneg_right Hr (by norm_num)
    have H := abs_sub_le (f z) ((z 0 - 2) / 2) α
    dsimp only [V]
    nlinarith only [H, HE', Hcenter, mul_nonneg hB0 hb.le]
  have Hradial : |fderiv ℝ (terminalSinglePhase h) Y (Pi.single 0 1) - 1 / 2| ≤ R * b := by
    let d := fderiv ℝ F Y (Pi.single 0 1)
    have Hd : ‖d‖ ≤ A := by
      simpa only [Pi.norm_single, norm_one, mul_one] using
        ((fderiv ℝ F Y).le_opNorm (Pi.single 0 1)).trans (mul_le_mul_of_nonneg_right Hnorm (norm_nonneg _))
    have Hd0 : |d 0| ≤ A := (norm_le_pi_norm d 0).trans Hd
    have Hdw : |d 1| + |d 2| ≤ A * b / α := by
      have H1 := (Hwall 0).2
      have H2 := (Hwall 1).2
      change |d 1| ≤ A * |u| / α at H1
      change |d 2| ≤ A * |w| / α at H2
      have Hsum := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hA0) hα.1.le
      rw [mul_add, add_div] at Hsum
      linarith only [H1, H2, Hsum]
    let S := exitTailLength η α J
    have hS : 0 ≤ S := exitTailLength_nonneg ⟨hη, hηhi.trans (by norm_num)⟩ hα J
    have HS : α * (1 + S) ≤ L := by
      have Hlog := Real.log_le_log (one_div_pos.mpr hη) (one_div_le_one_div_of_le hη₀.1 hηlo)
      have H := (exitTailLength_weighted_bounds ⟨hη, hηhi.trans (by norm_num)⟩ hα J).1
      dsimp only [L]
      nlinarith only [H, Hlog, hα.2]
    have HbT : b ^ 2 * (1 + S) ^ 2 ≤ L ^ 2 * b := by
      have H1 := mul_le_mul_of_nonneg_right hbα (by positivity : 0 ≤ b * (1 + S) ^ 2)
      have H2 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity : 0 ≤ α * (1 + S)) HS 2) hb.le
      nlinarith only [H1, H2]
    have HdR : |d 0 - 1| ≤ A * (1 + L ^ 2) * b := Hrad.trans (by
      have Hu : |u| ≤ b := (le_add_of_nonneg_right (abs_nonneg w)).trans hsum
      nlinarith only [mul_le_mul_of_nonneg_left (add_le_add Hu HbT) hA0])
    rw [Hder, ContinuousLinearMap.comp_apply]
    have H := clm_three_radial_composition_bound (fderiv ℝ f z) d
    refine H.trans ?_
    have H1 := mul_le_mul Hf0 Hd0 (abs_nonneg _) (mul_nonneg hP hb.le)
    have H2 := mul_le_mul Hfw Hdw (add_nonneg (abs_nonneg _) (abs_nonneg _)) (mul_nonneg hW hα.1.le)
    have Heq : (W * α) * (A * b / α) = W * A * b := by field_simp
    rw [Heq] at H2
    dsimp only [R]
    nlinarith only [H1, H2, HdR, (by positivity : 0 ≤ A * b * (1 + L ^ 2))]
  have Hnormf : ‖fderiv ℝ f z‖ ≤ 3 * (P + W + 1) := by
    apply clm_norm_le_card_mul_basis_bound _ (by positivity)
    intro i
    rw [Real.norm_eq_abs]
    fin_cases i
    · change |fderiv ℝ f z (Pi.single 0 1)| ≤ P + W + 1
      have H := abs_sub_le (fderiv ℝ f z (Pi.single 0 1)) (1 / 2) 0
      norm_num only [sub_zero, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at H
      nlinarith only [H, Hf0, mul_le_of_le_one_right hP hb1, hW]
    · change |fderiv ℝ f z (Pi.single 1 1)| ≤ P + W + 1
      nlinarith only [Hfw, mul_le_of_le_one_right hW hα.2, hP, abs_nonneg (fderiv ℝ f z (Pi.single 2 1))]
    · change |fderiv ℝ f z (Pi.single 2 1)| ≤ P + W + 1
      nlinarith only [Hfw, mul_le_of_le_one_right hW hα.2, hP, abs_nonneg (fderiv ℝ f z (Pi.single 1 1))]
  refine ⟨HV, Hsmooth, ?_, ?_⟩
  · have HC : V + R ≤ C := by dsimp only [C]; linarith only [hN]
    nlinarith only [Hvalue, Hradial, mul_le_mul_of_nonneg_right HC hb.le]
  · rw [Hder]
    have H := (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul Hnormf Hnorm (norm_nonneg _) (by positivity))
    have HC : N ≤ C := by dsimp only [C]; linarith only [hV, hRad]
    exact H.trans ((show 3 * (P + W + 1) * A = N by dsimp only [N]; ring).le.trans HC)
