-- Prove2me | solution 1 for BianchiIX.exists_terminalWallFactor_bounds_uniform
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T23:26:12.482028+00:00
-- url     : https://prove2.me/submissions/e26bf189-45a7-4847-a7b7-2717eb8afdab

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveWallMultipliers
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_Dynamics_CoreTailMultipliers
import Definitions.Def_BianchiIX_TerminalConeData
import Theorems.Thm_BianchiIX_contDiffAt_coreTailMultiplier_two
import Theorems.Thm_BianchiIX_coreTailMultiplier_formula
import Theorems.Thm_BianchiIX_coreTail_regular_of_valid
import Theorems.Thm_BianchiIX_exists_coreTailMultiplier_bounds_uniform
import Theorems.Thm_BianchiIX_exists_terminalCyclicInput_derivative_uniform
import Theorems.Thm_BianchiIX_exists_terminal_axisCycle_endpoint_uniform
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

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiff_projectiveCycleDenom (n : WithTop ℕ∞) : ContDiff ℝ n projectiveCycleDenom := by
  unfold projectiveCycleDenom axisCycleDenom curvature
  fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.normalizedProjectiveWallMultiplier_pos (x : NormalizedState) (T : ℝ) (i : Fin 3) :
    0 < normalizedProjectiveWallMultiplier x T i := Real.exp_pos _

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

private theorem BianchiIX.coreTailMultiplier_pos (η : ℝ) (Y : CoreAngleState) (i : Fin 2) :
    0 < coreTailMultiplier η Y i := normalizedProjectiveWallMultiplier_pos _ _ _

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.terminalWallFactor_pos {h : ℝ} {Y : ExitTailState}
    (hH : 0 < projectiveCycleDenom (coreTailState h Y)) (i : Fin 2) :
    0 < terminalWallFactor h Y i :=
  div_pos (mul_pos (by norm_num) (coreTailMultiplier_pos h Y i)) hH

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.terminalEntranceInput_wall_factors {h : ℝ} {Y : ExitTailState} (HV : coreTailValid h Y) :
    terminalEntranceInput h Y 1 = 4 * h / projectiveCycleDenom (coreTailState h Y) ∧
      terminalEntranceInput h Y 2 = Y 2 * terminalWallFactor h Y 1 ∧
      terminalEntranceInput h Y 3 = Y 1 * terminalWallFactor h Y 0 := by
  have H0 := coreTailMultiplier_formula HV 0
  have H1 := coreTailMultiplier_formula HV 1
  change coreTailState h Y 1 = Y 1 * coreTailMultiplier h Y 0 at H0
  change coreTailState h Y 3 = Y 2 * coreTailMultiplier h Y 1 at H1
  change (4 * coreTailState h Y 2 / _ = _) ∧ (4 * coreTailState h Y 3 / _ = _) ∧
    (4 * coreTailState h Y 1 / _ = _)
  rw [coreTailState_active HV, H0, H1]
  dsimp only [terminalWallFactor]
  constructor
  · rfl
  · constructor <;> ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_terminalWallFactor_two {h : ℝ} {Y : ExitTailState}
    (hR : 1 < Y 0) (HV : coreTailValid h Y)
    (hH : 0 < projectiveCycleDenom (coreTailState h Y)) (i : Fin 2) :
    ContDiffAt ℝ 2 (fun Z => terminalWallFactor h Z i) Y ∧
      ContDiffAt ℝ 2 (fun Z => Real.log (terminalWallFactor h Z i)) Y := by
  have HR := coreTail_regular_of_valid hR HV
  have HM := (contDiffAt_coreTailMultiplier_two hR HV HR.1 i).1
  have HD : ContDiffAt ℝ 2 (fun Z => projectiveCycleDenom (coreTailState h Z)) Y :=
    ContDiffAt.comp (g := projectiveCycleDenom) (f := coreTailState h) Y
    (contDiff_projectiveCycleDenom 2).contDiffAt HR.2.1
  have HB : ContDiffAt ℝ 2 (fun Z => terminalWallFactor h Z i) Y :=
    (contDiffAt_const.mul HM).div HD hH.ne'
  exact ⟨HB, HB.log (terminalWallFactor_pos hH i).ne'⟩

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.terminalWallFactor_log_fderiv {h : ℝ} {Y : ExitTailState}
    (hR : 1 < Y 0) (HV : coreTailValid h Y)
    (hH : 0 < projectiveCycleDenom (coreTailState h Y)) (i : Fin 2) :
    fderiv ℝ (fun Z => Real.log (terminalWallFactor h Z i)) Y =
      fderiv ℝ (fun Z => Real.log (coreTailMultiplier h Z i)) Y -
        fderiv ℝ (fun Z => Real.log (projectiveCycleDenom (coreTailState h Z))) Y := by
  have HR := coreTail_regular_of_valid hR HV
  have HM := (contDiffAt_coreTailMultiplier_two hR HV HR.1 i).2.differentiableAt (by norm_num)
  have HD : ContDiffAt ℝ 2 (fun Z => projectiveCycleDenom (coreTailState h Z)) Y :=
    ContDiffAt.comp (g := projectiveCycleDenom) (f := coreTailState h) Y
    (contDiff_projectiveCycleDenom 2).contDiffAt HR.2.1
  have HL := (HD.log hH.ne').differentiableAt (by norm_num)
  have HE : (fun Z => Real.log (terminalWallFactor h Z i)) =ᶠ[𝓝 Y]
      (fun Z => Real.log 4 + Real.log (coreTailMultiplier h Z i) -
        Real.log (projectiveCycleDenom (coreTailState h Z))) := by
    filter_upwards [HD.continuousAt.eventually_ne hH.ne'] with Z hZ
    rw [terminalWallFactor, Real.log_div (mul_ne_zero (by norm_num) (coreTailMultiplier_pos h Z i).ne') hZ,
      Real.log_mul (by norm_num) (coreTailMultiplier_pos h Z i).ne']
  rw [HE.fderiv_eq, fderiv_fun_sub (HM.const_add (Real.log 4)) HL, fderiv_const_add]

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.terminalEntranceInput_active_log_fderiv {h : ℝ} {Y : ExitTailState}
    (hR : 1 < Y 0) (HV : coreTailValid h Y) (hh : 0 < h)
    (hH : 0 < projectiveCycleDenom (coreTailState h Y)) :
    fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z 1)) Y =
      -fderiv ℝ (fun Z => Real.log (projectiveCycleDenom (coreTailState h Z))) Y := by
  have HR := coreTail_regular_of_valid hR HV
  have HD : ContDiffAt ℝ 2 (fun Z => projectiveCycleDenom (coreTailState h Z)) Y :=
    ContDiffAt.comp (g := projectiveCycleDenom) (f := coreTailState h) Y
    (contDiff_projectiveCycleDenom 2).contDiffAt HR.2.1
  have HE : (fun Z => Real.log (terminalEntranceInput h Z 1)) =ᶠ[𝓝 Y]
      (fun Z => Real.log (4 * h) - Real.log (projectiveCycleDenom (coreTailState h Z))) := by
    filter_upwards [HR.2.2, HD.continuousAt.eventually_ne hH.ne'] with Z hZ hZD
    rw [(terminalEntranceInput_wall_factors hZ).1,
      Real.log_div (mul_ne_zero (by norm_num) hh.ne') hZD]
  rw [HE.fderiv_eq, fderiv_const_sub]

end
end


/-- Formula (D.25), including the sharper inverse and logarithmic derivative powers, for the actual entrance. -/
theorem solution {η₀ : ℝ} (hη₀ : 0 < η₀ ∧ η₀ ≤ 1 / 100)
    {J : ℕ} (hJ : 2 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ 1 / 100 → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let z := terminalEntranceInput h Y
      coreTailValid h Y ∧ z 2 = w * terminalWallFactor h Y 1 ∧ z 3 = u * terminalWallFactor h Y 0 ∧
        (η / 2 * α ^ (J - 2) ≤ z 1 ∧ z 1 ≤ 2 * η * α ^ (J - 2)) ∧
        ‖fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z 1)) Y‖ ≤ C / α ∧
        ∀ i : Fin 2, 0 < terminalWallFactor h Y i ∧
          ContDiffAt ℝ 2 (fun Z => terminalWallFactor h Z i) Y ∧
          ContDiffAt ℝ 2 (fun Z => Real.log (terminalWallFactor h Z i)) Y ∧
          terminalWallFactor h Y i ≤ C / α ^ 2 ∧
          (terminalWallFactor h Y i)⁻¹ ≤ C * α ^ 2 ∧
          ‖fderiv ℝ (fun Z => Real.log (terminalWallFactor h Z i)) Y‖ ≤ C / α := by
  have hJ1 : 1 ≤ J := by omega
  obtain ⟨A, hA, εm, hεm, HM⟩ := exists_coreTailMultiplier_bounds_uniform
    ⟨hη₀.1, by linarith only [hη₀.2]⟩ hJ1
  obtain ⟨B, hB, εd, hεd, HD⟩ := exists_terminalCyclicInput_derivative_uniform hη₀ hJ1
  obtain ⟨_, _, εg, hεg, HG⟩ := exists_terminal_axisCycle_endpoint_uniform hη₀ hJ
  let C := 4 * A + B
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have h4A : 4 * A ≤ C := by dsimp only [C]; linarith only [hB]
  have h2A : 2 * A ≤ C := by dsimp only [C]; linarith only [hA, hB]
  have hAB : A + B ≤ C := by dsimp only [C]; linarith only [hA]
  have hBC : B ≤ C := by dsimp only [C]; linarith only [hA]
  refine ⟨C, hB.trans hBC, min εm (min εd εg), lt_min hεm (lt_min hεd hεg), ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum Y h z
  have hα0 : 0 < α := hα.1
  have hη : 0 < η := hη₀.1.trans_le hηlo
  have hη1 : η < 1 := by linarith only [hηhi]
  have hsm : b ≤ εm * α ^ J := hsmall.trans
    ((mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hα.1.le (2 * J))).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hα.1.le hα.2 (by omega)) hεm.le))
  have hsd := hsmall.trans (mul_le_mul_of_nonneg_right
    ((min_le_right _ _).trans (min_le_left _ _)) (pow_nonneg hα.1.le (2 * J)))
  have hsg := hsmall.trans (mul_le_mul_of_nonneg_right
    ((min_le_right _ _).trans (min_le_right _ _)) (pow_nonneg hα.1.le (2 * J)))
  obtain ⟨HV, Hmult⟩ := HM η α b u w hηlo hη1 hα hb hsm hsum
  change coreTailValid h Y at HV
  have HlogH : ‖fderiv ℝ (fun Z => Real.log (projectiveCycleDenom (coreTailState h Z))) Y‖ ≤ B / α :=
    (HD η α b u w hηlo hηhi hα hb hsd hsum).2.2.2
  obtain ⟨_, _, HH, _, _, HU, _⟩ := HG η α b u w hηlo hηhi hα hb hsg hsum
  change 399 / 100 * α ^ 2 < projectiveCycleDenom (coreTailState h Y) ∧
    projectiveCycleDenom (coreTailState h Y) < 401 / 100 * α ^ 2 at HH
  have Hlow : α ^ 2 ≤ projectiveCycleDenom (coreTailState h Y) := by nlinarith only [HH.1, sq_nonneg α]
  have Hhigh : projectiveCycleDenom (coreTailState h Y) ≤ 8 * α ^ 2 := by nlinarith only [HH.2, sq_nonneg α]
  have hH : 0 < projectiveCycleDenom (coreTailState h Y) := (sq_pos_of_pos hα.1).trans_le Hlow
  have hR : 1 < Y 0 := by change 1 < 2 + 2 * α; linarith only [hα.1]
  have Hfac := terminalEntranceInput_wall_factors HV
  refine ⟨HV, Hfac.2.1, Hfac.2.2, HU, ?_, ?_⟩
  · rw [terminalEntranceInput_active_log_fderiv hR HV (mul_pos hη (pow_pos hα.1 J)) hH, norm_neg]
    exact HlogH.trans (div_le_div_of_nonneg_right hBC hα.1.le)
  · intro i
    have Hmi := Hmult i
    change ContDiffAt ℝ 2 (fun Z => coreTailMultiplier h Z i) Y ∧
      ContDiffAt ℝ 2 (fun Z => Real.log (coreTailMultiplier h Z i)) Y ∧
      1 / A ≤ coreTailMultiplier h Y i ∧ coreTailMultiplier h Y i ≤ A ∧
      ‖fderiv ℝ (fun Z => Real.log (coreTailMultiplier h Z i)) Y‖ ≤ A / α at Hmi
    have Hsmooth := contDiffAt_terminalWallFactor_two hR HV hH i
    have hM : 0 < coreTailMultiplier h Y i := coreTailMultiplier_pos h Y i
    refine ⟨terminalWallFactor_pos hH i, Hsmooth.1, Hsmooth.2, ?_, ?_, ?_⟩
    · change 4 * coreTailMultiplier h Y i / projectiveCycleDenom (coreTailState h Y) ≤ C / α ^ 2
      exact (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hα.1) Hlow).trans
        (div_le_div_of_nonneg_right
          ((mul_le_mul_of_nonneg_left Hmi.2.2.2.1 (by norm_num : (0 : ℝ) ≤ 4)).trans h4A) (sq_nonneg α))
    · rw [terminalWallFactor, inv_div]
      apply (div_le_iff₀ (mul_pos (by norm_num) hM)).mpr
      have HAM : 1 ≤ coreTailMultiplier h Y i * A := (div_le_iff₀ hA0).mp Hmi.2.2.1
      have Hprod := mul_le_mul_of_nonneg_right HAM (sq_nonneg α)
      have HC := mul_le_mul_of_nonneg_right h2A
        (mul_nonneg (sq_nonneg α) (mul_pos (by norm_num : (0 : ℝ) < 4) hM).le)
      nlinarith only [Hhigh, Hprod, HC]
    · rw [terminalWallFactor_log_fderiv hR HV hH i]
      exact (norm_sub_le _ _).trans ((add_le_add Hmi.2.2.2.2 HlogH).trans
        (by rw [← add_div]; exact div_le_div_of_nonneg_right hAB hα.1.le))
