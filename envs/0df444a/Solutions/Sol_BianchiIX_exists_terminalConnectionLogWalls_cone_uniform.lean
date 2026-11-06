-- Prove2me | solution 1 for BianchiIX.exists_terminalConnectionLogWalls_cone_uniform
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T23:30:30.111496+00:00
-- url     : https://prove2.me/submissions/5f8570ed-e0f0-4a0a-b68e-04496d71430e

import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_TerminalConeData
import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Definitions.Def_BianchiIX_EntrancePhaseResponseData
import Theorems.Thm_BianchiIX_coreTail_regular_of_valid
import Theorems.Thm_BianchiIX_entranceReturn_regular
import Theorems.Thm_BianchiIX_entranceReturn_walls_pos
import Theorems.Thm_BianchiIX_exists_entrance_return_full_columns
import Theorems.Thm_BianchiIX_exists_terminalEntranceInput_cone_uniform
import Theorems.Thm_BianchiIX_exists_terminalWallFactor_bounds_uniform
import Theorems.Thm_BianchiIX_exists_terminal_axisCycle_endpoint_uniform
import Theorems.Thm_BianchiIX_exists_terminal_cycle_entrance_inputs_uniform
import Theorems.Thm_BianchiIX_terminal_log_composition_bounds
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

noncomputable section
open BianchiIX
open Filter Set
open scoped Topology

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

private theorem BianchiIX.contDiffAt_projectiveCycle (n : WithTop ℕ∞) {y : ProjectiveState}
    (hH : projectiveCycleDenom y ≠ 0) : ContDiffAt ℝ n projectiveCycle y := by
  have hD := (contDiff_projectiveCycleDenom n).contDiffAt (x := y)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · change ContDiffAt ℝ n (fun z : ProjectiveState => 1 - 4 * (z 0 + 1) / projectiveCycleDenom z) y
    fun_prop (disch := assumption)
  all_goals
    change ContDiffAt ℝ n (fun z : ProjectiveState => 4 * z _ / projectiveCycleDenom z) y
    fun_prop (disch := assumption)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.terminalConnection_regular_of_entrance {h : ℝ} {Y : ExitTailState}
    (hR : 1 < Y 0) (HV : coreTailValid h Y) (hH : projectiveCycleDenom (coreTailState h Y) ≠ 0) :
    let z := projectiveCycle (coreTailState h Y)
    7 / 4 ≤ coreRadius (z 0) (z 2) → 1 ≤ z 0 →
    (0 ≤ z 1 ∧ z 1 ≤ 1 / 10000) → (0 < z 2 ∧ z 2 < 1) →
    (0 ≤ z 3 ∧ z 3 ≤ 1 / 10000) →
    ContDiffAt ℝ 2 (terminalConnectionTime h) Y ∧ ContDiffAt ℝ 2 (terminalConnectionState h) Y := by
  intro z hk hm hu hv hw
  have HT := coreTail_regular_of_valid hR HV
  have HC := (contDiffAt_projectiveCycle 2 hH).comp Y HT.2.1
  have HE := entranceReturn_regular hk hm hu hv hw
  have Htime : ContDiffAt ℝ 2 (fun Z => entranceReturnTime (projectiveCycle (coreTailState h Z))) Y :=
    ContDiffAt.comp (g := entranceReturnTime) (f := projectiveCycle ∘ coreTailState h) Y HE.2.1 HC
  have Hstate : ContDiffAt ℝ 2 (fun Z => entranceReturnState (projectiveCycle (coreTailState h Z))) Y :=
    ContDiffAt.comp (g := entranceReturnState) (f := projectiveCycle ∘ coreTailState h) Y HE.2.2.1 HC
  exact ⟨HT.1.add Htime, Hstate⟩

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
open Set

private theorem BianchiIX.EntranceRadialInverseAt.hasFDerivAt_return {y : ProjectiveState}
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) :
    HasFDerivAt (fun z => entranceReturnState (Ψ z))
      ((fderiv ℝ entranceReturnState y).comp (entranceRadialInverseDifferential y)) (entranceRadialCoordinates y) := by
  have hd : HasFDerivAt entranceReturnState (fderiv ℝ entranceReturnState y) (Ψ (entranceRadialCoordinates y)) := by
    rw [HΨ.apply_base]
    exact ((entranceReturn_regular hk hm hu hv hw).2.2.1.differentiableAt (by norm_num)).hasFDerivAt
  simpa only [Function.comp_def] using hd.comp (entranceRadialCoordinates y) HΨ.hasFDerivAt

end
end

private theorem BianchiIX.terminalConnectionLogWalls_chart_germ {h : ℝ} {Y : ExitTailState}
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt (terminalCyclicInput h Y) Ψ)
    (hc : ContinuousAt (terminalCyclicInput h) Y) :
    terminalConnectionLogWalls h =ᶠ[𝓝 Y] (fun Z =>
      entranceLogWalls 1 (entranceReturnState (Ψ (terminalEntranceInput h Z)))) := by
  filter_upwards [hc.tendsto.eventually HΨ.left_inverse] with Z hZ
  change Ψ (terminalEntranceInput h Z) = terminalCyclicInput h Z at hZ
  rw [hZ]
  rfl

private theorem BianchiIX.terminalConnectionLogWalls_differential {h : ℝ} {Y : ExitTailState}
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt (terminalCyclicInput h Y) Ψ)
    (hc : ContinuousAt (terminalCyclicInput h) Y)
    (hz : DifferentiableAt ℝ (terminalEntranceInput h) Y)
    (hL : DifferentiableAt ℝ (fun z => entranceLogWalls 1 (entranceReturnState (Ψ z)))
      (terminalEntranceInput h Y)) :
    DifferentiableAt ℝ (terminalConnectionLogWalls h) Y ∧ ∀ d : ExitTailState,
      fderiv ℝ (terminalConnectionLogWalls h) Y d =
        fderiv ℝ (fun z => entranceLogWalls 1 (entranceReturnState (Ψ z)))
          (terminalEntranceInput h Y) (fderiv ℝ (terminalEntranceInput h) Y d) := by
  have HE := terminalConnectionLogWalls_chart_germ HΨ hc
  have HD := hL.hasFDerivAt.comp Y hz.hasFDerivAt
  refine ⟨HD.differentiableAt.congr_of_eventuallyEq HE, ?_⟩
  intro d
  rw [HE.fderiv_eq]
  exact congrArg (fun L : ExitTailState →L[ℝ] (Fin 2 → ℝ) => L d) HD.fderiv


/-- Formula (D.36) with separate logarithmic output rows and constants independent of both old walls. -/
theorem solution :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 1000 ∧ ∀ η₀ : ℝ, (0 < η₀ ∧ η₀ ≤ δ) →
      ∀ J : ℕ, 2 ≤ J → ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ δ → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let L := -Real.log (terminalEntranceInput h Y 2)
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalConnectionState h) Y ∧
        0 < terminalConnectionState h Y 1 ∧ 0 < terminalConnectionState h Y 3 ∧
        DifferentiableAt ℝ (terminalConnectionLogWalls h) Y ∧
        ∀ d : ExitTailState, d 0 = 1 → |d 1| ≤ Real.sqrt u → |d 2| ≤ Real.sqrt w →
          |fderiv ℝ (terminalConnectionLogWalls h) Y d 0| ≤
            C * ((1 + L) / α ^ 2 + 1 / (α * Real.sqrt w)) ∧
          |fderiv ℝ (terminalConnectionLogWalls h) Y d 1| ≤
            C * (L + 1 / α + 1 / Real.sqrt w + 1 / Real.sqrt u) := by
  obtain ⟨A, hA, εin, hεin, hεinhi, HA⟩ := exists_entrance_return_full_columns
  let δ := min (εin / 4) (1 / 1000)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  refine ⟨δ, hδ, min_le_right _ _, ?_⟩
  intro η₀ hη₀ J hJ
  have hη₀hi : η₀ ≤ 1 / 1000 := hη₀.2.trans (min_le_right _ _)
  have hη₀hi' : η₀ ≤ 1 / 100 := hη₀hi.trans (by norm_num)
  obtain ⟨B, hB, εc, hεc, HC⟩ := exists_terminalEntranceInput_cone_uniform ⟨hη₀.1, hη₀hi⟩ hJ
  obtain ⟨E, hE, εm, hεm, HM⟩ := exists_terminalWallFactor_bounds_uniform ⟨hη₀.1, hη₀hi'⟩ hJ
  obtain ⟨εi, hεi, HI⟩ := exists_terminal_cycle_entrance_inputs_uniform hεin ⟨hη₀.1, hη₀hi'⟩ (q := 0) hJ
  obtain ⟨_, _, εg, hεg, HG⟩ := exists_terminal_axisCycle_endpoint_uniform ⟨hη₀.1, hη₀hi'⟩ hJ
  let D := B + E
  have hBD : B ≤ D := by dsimp only [D]; linarith only [hE]
  have hED : E ≤ D := by dsimp only [D]; linarith only [hB]
  have hD : 1 ≤ D := hB.trans hBD
  have hD0 : 0 ≤ D := le_trans (by norm_num) hD
  have hA1 : 1 ≤ A + 1 := by linarith only [hA]
  let ε := min εc (min εm (min εi (min εg 1)))
  have hε : 0 < ε := lt_min hεc (lt_min hεm (lt_min hεi (lt_min hεg (by norm_num))))
  refine ⟨8 * (A + 1) * D, by nlinarith only [hA1, hD, mul_le_mul_of_nonneg_left hD (by linarith only [hA] : 0 ≤ A + 1)],
    ε, hε, ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum hu hw Y h L
  have hα0 : 0 < α := hα.1
  have hη1000 : η ≤ 1 / 1000 := hηhi.trans (min_le_right _ _)
  have hη100 : η ≤ 1 / 100 := hη1000.trans (by norm_num)
  have hηin : η ≤ εin / (4 * (11 / 5) ^ (0 : ℕ)) := by
    simpa only [pow_zero, mul_one] using hηhi.trans (min_le_left _ _)
  have small {a : ℝ} (ha : ε ≤ a) : b ≤ a * α ^ (2 * J) :=
    hsmall.trans (mul_le_mul_of_nonneg_right ha (pow_nonneg hα.1.le _))
  have hεm' : ε ≤ εm := (min_le_right _ _).trans (min_le_left _ _)
  have hεi' : ε ≤ εi := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεg' : ε ≤ εg := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hε1 : ε ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨HV, Hreg, Hz, Hcone⟩ := HC η α b u w hηlo hη1000 hα hb (small (min_le_left _ _)) hsum hu hw
  obtain ⟨_, _, Hweak, _, _, Hfactor⟩ := HM η α b u w hηlo hη100 hα hb (small hεm') hsum
  obtain ⟨_, _, HK, Hm, Hu, Hv, Hw, _, HH⟩ := HI η α b u w hηlo hη100 hηin hα hb (small hεi') hsum hu hw
  obtain ⟨_, _, _, _, Hk, _⟩ := HG η α b u w hηlo hη100 hα hb (small hεg') hsum
  let y := terminalCyclicInput h Y
  let z := terminalEntranceInput h Y
  let k := coreRadius (y 0) (y 2)
  change 7 / 4 < k at HK
  change 0 < y 2 ∧ y 2 < 1 / 2 at Hv
  change z 3 = u * terminalWallFactor h Y 0 at Hweak
  have hk : 1 / α ≤ k ∧ k ≤ 3 / α := by
    change 19 / (10 * α) < k ∧ k < 11 / (5 * α) at Hk
    constructor
    · apply le_trans _ Hk.1.le
      apply (div_le_div_iff₀ hα.1 (by positivity : 0 < 10 * α)).mpr
      linarith only [hα.1]
    · apply Hk.2.le.trans
      apply (div_le_div_iff₀ (by positivity : 0 < 5 * α) hα.1).mpr
      linarith only [hα.1]
  have hm : 1 ≤ y 0 := by change 2 < y 0 at Hm; linarith only [Hm]
  have hv : 0 < y 2 ∧ y 2 < 1 := ⟨Hv.1, by linarith only [Hv.2]⟩
  have hu' : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000 := ⟨Hu.1.le, Hu.2.1.trans hεinhi⟩
  have hw' : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000 := ⟨Hw.1.le, Hw.2.1.trans hεinhi⟩
  have hin1 : εin ≤ 1 := hεinhi.trans (by norm_num)
  have hR : 1 < Y 0 := by change 1 < 2 + 2 * α; linarith only [hα.1]
  have Hstate := (terminalConnection_regular_of_entrance hR HV HH.ne' HK.le hm hu' hv hw').2
  have Hcyc : ContDiffAt ℝ 2 (terminalCyclicInput h) Y :=
    ContDiffAt.comp (g := projectiveCycle) (f := coreTailState h) Y
      (contDiffAt_projectiveCycle 2 HH.ne') (coreTail_regular_of_valid hR HV).2.1
  have HR := entranceReturn_regular HK.le hm hu' hv hw'
  have Hpos := entranceReturn_walls_pos HK.le hm ⟨Hu.1, hu'.2⟩ hv ⟨Hw.1, hw'.2⟩
    (entranceReturnTime y) ⟨HR.1.1.1.1.le, le_rfl⟩
  obtain ⟨Ψ, HΨ, _, HU, HW⟩ := HA y 1 HK.le hm ⟨Hu.1, Hu.2.1⟩ hv ⟨Hw.1, Hw.2.1⟩ (Or.inl rfl)
  let F := fun z => entranceLogWalls 1 (entranceReturnState (Ψ z))
  have HF : DifferentiableAt ℝ F z := by
    have Hlog : DifferentiableAt ℝ (entranceLogWalls 1) (entranceReturnState (Ψ z)) := by
      change DifferentiableAt ℝ (entranceLogWalls 1) (entranceReturnState (Ψ (entranceRadialCoordinates y)))
      rw [HΨ.apply_base]
      exact (hasFDerivAt_entranceLogWalls 1 Hpos.1.ne' Hpos.2.2.ne').differentiableAt
    exact Hlog.comp z (HΨ.hasFDerivAt_return HK.le hm hu' hv hw').differentiableAt
  have Hd := terminalConnectionLogWalls_differential HΨ Hcyc.continuousAt (Hreg.differentiableAt (by norm_num)) HF
  have hL : 0 ≤ L := neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le)
  have hb1 : b ≤ 1 := (hsmall.trans (mul_le_of_le_one_right hε.le (pow_le_one₀ hα.1.le hα.2))).trans hε1
  have hu1 : u ≤ 1 := by linarith only [le_abs_self u, abs_nonneg w, hsum, hb1]
  have hwt : y 3 * (1 / Real.sqrt u) ≤ D / α ^ 2 := by
    change z 3 * (1 / Real.sqrt u) ≤ D / α ^ 2
    calc
      _ = terminalWallFactor h Y 0 * (u / Real.sqrt u) := by rw [Hweak]; ring
      _ = terminalWallFactor h Y 0 * Real.sqrt u := by rw [Real.div_sqrt]
      _ ≤ terminalWallFactor h Y 0 := mul_le_of_le_one_right (Hfactor 0).1.le (Real.sqrt_le_one.mpr hu1)
      _ ≤ E / α ^ 2 := (Hfactor 0).2.2.2.1
      _ ≤ D / α ^ 2 := div_le_div_of_nonneg_right hED (sq_nonneg α)
  refine ⟨HV, Hstate, Hpos.1, Hpos.2.2, Hd.1, ?_⟩
  intro d hd0 hd1 hd2
  obtain ⟨Hr, Hlu, Hlv, Hlw⟩ := Hcone d hd0 hd1 hd2
  let e := fderiv ℝ (terminalEntranceInput h) Y d
  have Hcomponent (i : Fin 3) : e i.succ = z i.succ *
      fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z i.succ)) Y d := by
    have H := hasFDerivAt_pi'.mp (Hreg.differentiableAt (by norm_num)).hasFDerivAt i.succ
    rw [(H.log (Hz i).1.ne').fderiv]
    simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
    change e i.succ = z i.succ * ((z i.succ)⁻¹ * e i.succ)
    rw [← mul_assoc, mul_inv_cancel₀ (show z i.succ ≠ 0 from (Hz i).1.ne'), one_mul]
  have Hscaled (i : Fin 3) {K : ℝ}
      (H : |fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z i.succ)) Y d| ≤ K) : |e i.succ| ≤ z i.succ * K := by
    rw [Hcomponent i, abs_mul, abs_of_pos (Hz i).1]
    exact mul_le_mul_of_nonneg_left H (Hz i).1.le
  have Hrd : |e 0| ≤ D / α ^ 2 := by
    have H0 := congrArg (fun T : ExitTailState →L[ℝ] ℝ => T d)
      (fderiv_apply (Hreg.differentiableAt (by norm_num)) 0)
    change fderiv ℝ (fun Z => terminalEntranceInput h Z 0) Y d = e 0 at H0
    rw [← H0]
    exact Hr.trans (div_le_div_of_nonneg_right hBD (sq_nonneg α))
  have Hbd := div_le_div_of_nonneg_right hBD hα.1.le
  have HAA : A ≤ A + 1 := by linarith
  have H := terminal_log_composition_bounds (fderiv ℝ F z) e hA1 hD hα hk
    ⟨Hu.1, Hu.2.1.trans hin1⟩ hv.1 ⟨Hw.1, Hw.2.1.trans hin1⟩ hL
    (by positivity : 0 ≤ 1 / Real.sqrt w) (by positivity : 0 ≤ 1 / Real.sqrt u) hwt Hrd
    (Hscaled 0 (Hlu.trans Hbd)) (Hscaled 1 (Hlv.trans (add_le_add Hbd le_rfl)))
    (Hscaled 2 (Hlw.trans (add_le_add Hbd le_rfl)))
    (HU.1.trans (mul_le_mul_of_nonneg_right HAA hL)) (HU.2.1.trans HAA)
    (HU.2.2.1.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right HAA (by linarith only [HK] : 0 ≤ k)) hv.1.le))
    (HU.2.2.2.trans HAA)
    (HW.1.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right HAA hL) (sq_nonneg k)))
    (HW.2.1.trans (div_le_div_of_nonneg_right HAA (sq_nonneg k)))
    (HW.2.2.1.trans (div_le_div_of_nonneg_right HAA hv.1.le))
    (HW.2.2.2.trans (div_le_div_of_nonneg_right HAA (sq_nonneg k)))
  rw [Hd.2 d]
  have hfrac : 1 / Real.sqrt w / α = 1 / (α * Real.sqrt w) := by ring
  rw [hfrac] at H
  exact H
