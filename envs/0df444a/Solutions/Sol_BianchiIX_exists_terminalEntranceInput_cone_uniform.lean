-- Prove2me | solution 1 for BianchiIX.exists_terminalEntranceInput_cone_uniform
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T23:27:47.18533+00:00
-- url     : https://prove2.me/submissions/121e26e3-2f6d-4b6c-b2ed-85643fb70613

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_Dynamics_CoreTailMultipliers
import Definitions.Def_BianchiIX_TerminalConeData
import Theorems.Thm_BianchiIX_coreTailMultiplier_formula
import Theorems.Thm_BianchiIX_coreTail_regular_of_valid
import Theorems.Thm_BianchiIX_exists_terminalEntranceInput_derivative_uniform
import Theorems.Thm_BianchiIX_exists_terminalWallFactor_bounds_uniform
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
open Filter
open scoped Topology

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

private theorem BianchiIX.terminalEntranceInput_passive_log_fderiv {h : ℝ} {Y : ExitTailState}
    (hR : 1 < Y 0) (HV : coreTailValid h Y) (i : Fin 2)
    (hy : Y i.succ ≠ 0) (hB : terminalWallFactor h Y i ≠ 0)
    (HB : ContDiffAt ℝ 2 (fun Z => terminalWallFactor h Z i) Y) :
    ContDiffAt ℝ 2 (fun Z => Real.log (terminalEntranceInput h Z (if i = 0 then 3 else 2))) Y ∧
      ∀ d : ExitTailState,
        fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z (if i = 0 then 3 else 2))) Y d =
          d i.succ / Y i.succ + fderiv ℝ (fun Z => Real.log (terminalWallFactor h Z i)) Y d := by
  have HY : ContDiffAt ℝ 2 (fun Z : ExitTailState => Real.log (Z i.succ)) Y :=
    (contDiffAt_apply ℝ ℝ i.succ Y).log hy
  have HL := HB.log hB
  have HE : (fun Z => Real.log (terminalEntranceInput h Z (if i = 0 then 3 else 2))) =ᶠ[𝓝 Y]
      (fun Z => Real.log (Z i.succ) + Real.log (terminalWallFactor h Z i)) := by
    filter_upwards [(coreTail_regular_of_valid hR HV).2.2,
      (continuousAt_apply i.succ Y).eventually_ne hy, HB.continuousAt.eventually_ne hB] with Z hZ hyZ hBZ
    have H : terminalEntranceInput h Z (if i = 0 then 3 else 2) = Z i.succ * terminalWallFactor h Z i := by
      fin_cases i
      · exact (terminalEntranceInput_wall_factors hZ).2.2
      · exact (terminalEntranceInput_wall_factors hZ).2.1
    rw [H, Real.log_mul hyZ hBZ]
  refine ⟨(HY.add HL).congr_of_eventuallyEq HE, ?_⟩
  intro d
  have HD := ((hasFDerivAt_apply (𝕜 := ℝ) i.succ Y).log hy).add
    (HL.differentiableAt (by norm_num)).hasFDerivAt
  change HasFDerivAt (fun Z => Real.log (Z i.succ) + Real.log (terminalWallFactor h Z i)) _ Y at HD
  rw [HE.fderiv_eq, HD.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [div_eq_mul_inv, mul_comm]


/-- Formula (D.35) for every normalized square-root cone direction, with no wall-ratio condition. -/
theorem solution {η₀ : ℝ} (hη₀ : 0 < η₀ ∧ η₀ ≤ 1 / 1000)
    {J : ℕ} (hJ : 2 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ 1 / 1000 → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let z := terminalEntranceInput h Y
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalEntranceInput h) Y ∧
        (∀ i : Fin 3, 0 < z i.succ ∧
          ContDiffAt ℝ 2 (fun Z => Real.log (terminalEntranceInput h Z i.succ)) Y) ∧
        ∀ d : ExitTailState, d 0 = 1 → |d 1| ≤ Real.sqrt u → |d 2| ≤ Real.sqrt w →
          |fderiv ℝ (fun Z => terminalEntranceInput h Z 0) Y d| ≤ C / α ^ 2 ∧
          |fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z 1)) Y d| ≤ C / α ∧
          |fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z 2)) Y d| ≤ C / α + 1 / Real.sqrt w ∧
          |fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z 3)) Y d| ≤ C / α + 1 / Real.sqrt u := by
  obtain ⟨A, hA, εd, hεd, HD⟩ := exists_terminalEntranceInput_derivative_uniform hη₀ hJ
  obtain ⟨B, hB, εm, hεm, HM⟩ := exists_terminalWallFactor_bounds_uniform
    ⟨hη₀.1, by linarith only [hη₀.2]⟩ hJ
  let C := A + B
  have hAC : A ≤ C := by dsimp only [C]; linarith only [hB]
  have hBC : B ≤ C := by dsimp only [C]; linarith only [hA]
  let ε := min εd (min εm 1)
  have hε : 0 < ε := lt_min hεd (lt_min hεm (by norm_num))
  refine ⟨C, hA.trans hAC, ε, hε, ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum hu hw Y h z
  have hsd := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left εd (min εm 1))
    (pow_nonneg hα.1.le (2 * J)))
  have hsm := hsmall.trans (mul_le_mul_of_nonneg_right
    ((min_le_right εd (min εm 1)).trans (min_le_left εm 1)) (pow_nonneg hα.1.le (2 * J)))
  have hb1 : b ≤ 1 := (hsmall.trans (mul_le_of_le_one_right hε.le
    (pow_le_one₀ hα.1.le hα.2))).trans ((min_le_right εd (min εm 1)).trans (min_le_right εm 1))
  have hsum' : u + w ≤ b := by simpa only [abs_of_pos hu, abs_of_pos hw] using hsum
  have hu1 : u ≤ 1 := by linarith only [hsum', hw, hb1]
  have hw1 : w ≤ 1 := by linarith only [hsum', hu, hb1]
  obtain ⟨HV, _, Hreg, _, Hder, _⟩ := HD η α b u w hηlo hηhi hα hb hsd hsum
  obtain ⟨_, Hv, Hw, Hu, Hlog, Hfactor⟩ := HM η α b u w hηlo
    (by linarith only [hηhi]) hα hb hsm hsum
  have Hz1 : 0 < z 1 := (mul_pos (div_pos (hη₀.1.trans_le hηlo) (by norm_num))
    (pow_pos hα.1 (J - 2))).trans_le Hu.1
  have Hz2 : 0 < z 2 := by change 0 < terminalEntranceInput h Y 2; rw [Hv]; exact mul_pos hw (Hfactor 1).1
  have Hz3 : 0 < z 3 := by change 0 < terminalEntranceInput h Y 3; rw [Hw]; exact mul_pos hu (Hfactor 0).1
  have Hz (i : Fin 3) : 0 < z i.succ := by fin_cases i <;> assumption
  have hR : 1 < Y 0 := by change 1 < 2 + 2 * α; linarith only [hα.1]
  refine ⟨HV, Hreg, fun i => ⟨Hz i, ((contDiffAt_pi.mp Hreg) i.succ).log (Hz i).ne'⟩, ?_⟩
  intro d hd0 hd1 hd2
  have hdnorm : ‖d‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    simp only [Real.norm_eq_abs]
    fin_cases i
    · simp [hd0]
    · exact hd1.trans (Real.sqrt_le_one.mpr hu1)
    · exact hd2.trans (Real.sqrt_le_one.mpr hw1)
  have Hbound (L : ExitTailState →L[ℝ] ℝ) {K : ℝ} (hL : ‖L‖ ≤ K) : |L d| ≤ K :=
    (L.le_opNorm d).trans ((mul_le_of_le_one_right (norm_nonneg L) hdnorm).trans hL)
  have Hpassive (i : Fin 2) (hy : 0 < Y i.succ) (hd : |d i.succ| ≤ Real.sqrt (Y i.succ)) :
      |fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z (if i = 0 then 3 else 2))) Y d| ≤
        C / α + 1 / Real.sqrt (Y i.succ) := by
    rw [(terminalEntranceInput_passive_log_fderiv hR HV i hy.ne' (Hfactor i).1.ne' (Hfactor i).2.1).2 d]
    have Hratio : |d i.succ / Y i.succ| ≤ 1 / Real.sqrt (Y i.succ) := by
      rw [abs_div, abs_of_pos hy]
      exact (div_le_div_of_nonneg_right hd hy.le).trans_eq Real.sqrt_div_self'
    have Hfactor' := Hbound _ (Hfactor i).2.2.2.2.2
    have Hconst := div_le_div_of_nonneg_right hBC hα.1.le
    exact (abs_add_le _ _).trans (by linarith only [Hratio, Hfactor', Hconst])
  refine ⟨?_, (Hbound _ Hlog).trans (div_le_div_of_nonneg_right hBC hα.1.le), Hpassive 1 hw hd2,
    Hpassive 0 hu hd1⟩
  rw [fderiv_apply (Hreg.differentiableAt (by norm_num))]
  exact (norm_le_pi_norm _ 0).trans (((fderiv ℝ (terminalEntranceInput h) Y).le_opNorm d).trans
    ((mul_le_of_le_one_right (norm_nonneg _) hdnorm).trans
      (Hder.trans (div_le_div_of_nonneg_right hAC (sq_nonneg α)))))
