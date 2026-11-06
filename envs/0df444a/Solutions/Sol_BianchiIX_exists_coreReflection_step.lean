-- Prove2me | solution 1 for BianchiIX.exists_coreReflection_step
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:35:17.108339+00:00
-- url     : https://prove2.me/submissions/f422ba6a-14b8-4257-aba3-7e9b8e225d63

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Definitions.Def_BianchiIX_EraReturnData
import Theorems.Thm_BianchiIX_coreRadiusReturn_exit_chart
import Theorems.Thm_BianchiIX_exists_coreRadiusReturn_estimates
import Theorems.Thm_BianchiIX_exists_reflectionReturn_phase_bounds
import Theorems.Thm_BianchiIX_positive_cone_transport
import Theorems.Thm_BianchiIX_projectiveOriginalFlow_restart
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
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
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX

private theorem BianchiIX.abs_log_le_twice_sub_one_of_half_le {t : ℝ} (ht : 1 / 2 ≤ t) :
    |Real.log t| ≤ 2 * |t - 1| := by
  have ht0 : 0 < t := by linarith only [ht]
  have ha := abs_nonneg (t - 1)
  have hlo := neg_le_abs (t - 1)
  have hhi := le_abs_self (t - 1)
  have hinv : 1 / t ≤ 1 + 2 * |t - 1| := (div_le_iff₀ ht0).mpr (by
    nlinarith only [hlo, mul_le_mul_of_nonneg_right ht ha])
  have Hlo := Real.one_sub_inv_le_log_of_pos ht0
  have Hhi := Real.log_le_sub_one_of_pos ht0
  rw [inv_eq_one_div] at Hlo
  exact abs_le.mpr ⟨by linarith only [Hlo, hinv], by linarith only [Hhi, hhi, ha]⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.coreRadiusReturnValid_denom_pos {Y : CoreAngleState} (H : coreRadiusReturnValid Y) :
    0 < projectiveStateDenom (coreRadiusEntry Y) := by
  have hzero := (H.2.1 0 ⟨le_rfl, H.1.1.1.le⟩).2
  rw [normalizedMaxCurve_initial] at hzero
  change 0 < 1 + (6 / projectiveStateDenom (coreRadiusEntry Y) - 1) at hzero
  by_contra! hn
  have HD := div_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 6) hn
  linarith only [hzero, HD]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_reflectionReturn_estimates :
    ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      31 / 8 ≤ Y 0 → (0 < Y 1 ∧ Y 1 ≤ ε / Y 0) → (0 < Y 2 ∧ Y 2 ≤ ε / Y 0) →
      IsLeast {t : ℝ | 0 < t ∧ projectiveOriginalFlow (coreTailEntry Y) 0 t 3 = 1}
        (reflectionReturnTime Y) ∧
      coreRadiusEntry (reflectionReturnState Y) =
        projectiveReflection (projectiveOriginalFlow (coreTailEntry Y) 0 (reflectionReturnTime Y)) ∧
      ContDiffAt ℝ 2 reflectionReturnTime Y ∧ ContDiffAt ℝ 2 reflectionReturnState Y ∧
      |reflectionReturnState Y 0 - (Y 0 - 2)| ≤ C * (Y 1 + Y 2) / Y 0 ∧
      (∀ i : Fin 2, 0 < reflectionReturnState Y i.succ ∧ reflectionReturnState Y i.succ ≤ Y i.succ) ∧
      ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
        let d := fderiv ℝ reflectionReturnState Y v
        1 / 2 ≤ d 0 ∧ |d 0 - 1| ≤ C * Real.sqrt (Y 1 + Y 2) / Y 0 ∧
          |Real.log (d 0)| ≤ C * Real.sqrt (Y 1 + Y 2) / Y 0 ∧
          ∀ i : Fin 2, |d i.succ| ≤ Real.sqrt (reflectionReturnState Y i.succ) * d 0 := by
  obtain ⟨ε, hε, hεmax, C, hC, H⟩ := exists_reflectionReturn_phase_bounds
  refine ⟨ε, hε, hεmax, 2 * C, by positivity, ?_⟩
  intro Y hR hu hw
  obtain ⟨hfirst, hactual, ht, hF, hval, hwalls, hderiv⟩ := H Y hR hu hw
  have hR0 : 0 < Y 0 := by linarith only [hR]
  have hscale {b : ℝ} (hb : 0 ≤ b) : C * b / Y 0 ≤ 2 * C * b / Y 0 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith only [hC]) hb) hR0.le
  refine ⟨hfirst, hactual, ht, hF, hval.trans (hscale (add_nonneg hu.1.le hw.1.le)), hwalls, ?_⟩
  intro v hv0 hv1 hv2 d
  obtain ⟨hmargin, herr, hcone⟩ := hderiv v hv0 hv1 hv2
  refine ⟨hmargin, herr.trans (hscale (Real.sqrt_nonneg _)), ?_, hcone⟩
  exact ((abs_log_le_twice_sub_one_of_half_le hmargin).trans
    (mul_le_mul_of_nonneg_left herr (by norm_num))).trans_eq (by ring)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreReflection_canonical_orbit {Y : CoreAngleState}
    (hcore : coreRadiusReturnValid Y)
    (hchart : coreTailEntry (coreReturnState coreRadiusReturnTime Y) =
      projectiveOriginalFlow (coreRadiusEntry Y) 0 (coreRadiusReturnTime Y))
    (ht : 0 < reflectionReturnTime (coreReturnState coreRadiusReturnTime Y))
    (hactual : coreRadiusEntry (reflectionReturnState (coreReturnState coreRadiusReturnTime Y)) =
      projectiveReflection (projectiveOriginalFlow (coreTailEntry (coreReturnState coreRadiusReturnTime Y)) 0
        (reflectionReturnTime (coreReturnState coreRadiusReturnTime Y)))) :
    0 < coreReflectionTime Y ∧
      coreRadiusEntry (coreReflectionState coreRadiusReturnTime Y) =
        projectiveReflection (projectiveOriginalFlow (coreRadiusEntry Y) 0 (coreReflectionTime Y)) := by
  have hT := hcore.1.1.1
  have hA := (hcore.2.1 (coreRadiusReturnTime Y) ⟨hT.le, le_rfl⟩).2
  have HR := projectiveOriginalFlow_restart (coreRadiusReturnValid_denom_pos hcore) hT.le ht.le hA
  rw [← hchart] at HR
  exact ⟨add_pos ht hT, hactual.trans (congrArg projectiveReflection HR)⟩

end
end


/-- One common amplitude domain supports the actual core-reflection step and its phase, loss and cone estimates. -/
theorem solution :
    ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), c ≤ 1 / 2 ∧
      ∀ Y : CoreAngleState, 2 ≤ Y 0 →
        (0 < Y 1 ∧ Y 1 ≤ ε / Y 0) → (0 < Y 2 ∧ Y 2 ≤ ε / Y 0) →
        let F := coreReturnState coreRadiusReturnTime
        let Z := F Y
        let G := coreReflectionState coreRadiusReturnTime
        coreRadiusReturnValid Y ∧ ContDiffAt ℝ 1 F Y ∧ |Z 0 - Y 0| ≤ 1 / 8 ∧
        (ContDiffAt ℝ 1 coreRadiusReturnTime Y ∧ |Z 0 - Y 0| ≤ C * (Y 1 + Y 2) / Y 0 ∧
          (∀ i : Fin 2, 0 < Z i.succ ∧ Z i.succ ≤ Real.exp (-c / Y 0) * Y i.succ) ∧
          ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
            let d := fderiv ℝ F Y v
            0 < d 0 ∧ |Real.log (d 0)| ≤ C * Real.sqrt (Y 1 + Y 2) / Y 0 ∧
              ∀ i : Fin 2, |d i.succ| ≤ Real.sqrt (Z i.succ) * d 0) ∧
        (31 / 8 ≤ Z 0 →
          0 < coreReflectionTime Y ∧
          coreRadiusEntry (G Y) = projectiveReflection
            (projectiveOriginalFlow (coreRadiusEntry Y) 0 (coreReflectionTime Y)) ∧
          ContDiffAt ℝ 1 coreReflectionTime Y ∧ ContDiffAt ℝ 1 G Y ∧
          |Z 0 - Y 0| + |G Y 0 - (Z 0 - 2)| ≤ C * (Y 1 + Y 2) / Y 0 ∧
          |G Y 0 - (Y 0 - 2)| ≤ C * (Y 1 + Y 2) / Y 0 ∧
          (3 / 2 ≤ Y 0 - G Y 0 ∧ Y 0 - G Y 0 ≤ 5 / 2) ∧
          (∀ i : Fin 2, 0 < Z i.succ ∧ 0 < G Y i.succ ∧ G Y i.succ ≤ Z i.succ ∧
            Z i.succ ≤ Real.exp (-c / Y 0) * Y i.succ) ∧
          (2 ≤ G Y 0 → ∀ i : Fin 2, G Y i.succ ≤ ε / G Y 0) ∧
          ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
            let d := fderiv ℝ G Y v
            0 < d 0 ∧ |Real.log (d 0)| ≤ C * Real.sqrt (Y 1 + Y 2) / Y 0 ∧
              ∀ i : Fin 2, |d i.succ| ≤ Real.sqrt (G Y i.succ) * d 0) := by
  obtain ⟨εk, hεk, _, K, hK, c, hc, hcmax, HK⟩ := exists_coreRadiusReturn_estimates
  obtain ⟨εr, hεr, _, R, hR, HR⟩ := exists_reflectionReturn_estimates
  let C := K + 2 * R
  have hC : 0 < C := by dsimp [C]; positivity
  let ε := min εk (min (εr / 2) (min (1 / 10000) (min (1 / (4 * K)) (1 / C))))
  have hε : 0 < ε := lt_min hεk (lt_min (half_pos hεr)
    (lt_min (by norm_num) (lt_min (by positivity) (by positivity))))
  have hεk' : ε ≤ εk := min_le_left _ _
  have hεr' : ε ≤ εr / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hεmax : ε ≤ 1 / 10000 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεK : ε ≤ 1 / (4 * K) := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hεC : ε ≤ 1 / C := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hKε : K * ε ≤ 1 / 4 := by
    have H := (le_div_iff₀ (by positivity : 0 < 4 * K)).mp hεK
    nlinarith only [H]
  have hCε : C * ε ≤ 1 := by simpa only [mul_comm] using (le_div_iff₀ hC).mp hεC
  refine ⟨ε, hε, hεmax, C, hC, c, hc, hcmax, ?_⟩
  intro Y hk hu hw F Z G
  have hk0 : 0 < Y 0 := by linarith only [hk]
  have hb : 0 ≤ Y 1 + Y 2 := add_nonneg hu.1.le hw.1.le
  have hbε : Y 1 + Y 2 ≤ ε := by
    nlinarith only [(le_div_iff₀ hk0).mp hu.2, (le_div_iff₀ hk0).mp hw.2,
      mul_le_mul_of_nonneg_right hk hu.1.le, mul_le_mul_of_nonneg_right hk hw.1.le]
  have hεscale := div_le_div_of_nonneg_right hεk' hk0.le
  obtain ⟨hvalid, ht, hF, hval, hwall, hdiff⟩ := HK Y hk
    ⟨hu.1.le, hu.2.trans hεscale⟩ ⟨hw.1.le, hw.2.trans hεscale⟩
  have hpos (i : Fin 2) : 0 < Y i.succ := by
    fin_cases i
    · exact hu.1
    · exact hw.1
  have hin (i : Fin 2) : Y i.succ ≤ ε / Y 0 := by
    fin_cases i
    · exact hu.2
    · exact hw.2
  have hzpos (i : Fin 2) : 0 < Z i.succ := (hwall i).2.1.mpr (hpos i)
  have hzle (i : Fin 2) : Z i.succ ≤ Y i.succ := (hwall i).2.2.trans
    ((mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) hk0.le))
      (hpos i).le).trans_eq (one_mul _))
  have hsmall : |Z 0 - Y 0| ≤ 1 / 8 := hval.trans (by
    calc
      _ ≤ K * ε / Y 0 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbε hK.le) hk0.le
      _ ≤ K * ε / 2 := div_le_div_of_nonneg_left (mul_nonneg hK.le hε.le) (by norm_num) hk
      _ ≤ _ := by linarith only [hKε])
  have hZrange : Y 0 / 2 ≤ Z 0 ∧ Z 0 ≤ 2 * Y 0 := by
    constructor <;> linarith only [(abs_le.mp hsmall).1, (abs_le.mp hsmall).2, hk]
  have hZ0 : 0 < Z 0 := (half_pos hk0).trans_le hZrange.1
  have hKC : K ≤ C := by dsimp [C]; linarith only [hR]
  have hcoefficient {a : ℝ} (ha : 0 ≤ a) : K * a / Y 0 ≤ C * a / Y 0 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hKC ha) hk0.le
  refine ⟨hvalid, hF, hsmall, ?_, ?_⟩
  · refine ⟨ht, hval.trans (hcoefficient hb), fun i => ⟨hzpos i, (hwall i).2.2⟩, ?_⟩
    intro v hv0 hv1 hv2 d
    obtain ⟨hm, hl, hcone⟩ := hdiff v hv0 hv1 hv2
    exact ⟨by linarith only [hm.1], hl.trans (hcoefficient (Real.sqrt_nonneg _)), hcone⟩
  intro hguard
  have hzquarter (i : Fin 2) : Z i.succ ≤ 1 / 4 :=
    ((hzle i).trans (hin i)).trans ((div_le_self hε.le (by linarith only [hk])).trans
      (hεmax.trans (by norm_num)))
  have hchart := coreRadiusReturn_exit_chart hvalid (by linarith only [hguard])
    ⟨(hzpos 0).le, hzquarter 0⟩ ⟨(hzpos 1).le, hzquarter 1⟩
  have hbudget : ε / Y 0 ≤ εr / Z 0 := by
    calc
      _ = (2 * ε) / (2 * Y 0) := by ring
      _ ≤ (2 * ε) / Z 0 := div_le_div_of_nonneg_left (by positivity) hZ0 hZrange.2
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith only [hεr']) hZ0.le
  obtain ⟨hfirst, hactual, hrt, hrf, hrval, hrwall, hrdiff⟩ := HR Z hguard
    ⟨hzpos 0, ((hzle 0).trans hu.2).trans hbudget⟩
    ⟨hzpos 1, ((hzle 1).trans hw.2).trans hbudget⟩
  obtain ⟨htotal, horbit⟩ := coreReflection_canonical_orbit hvalid hchart hfirst.1.1 hactual
  have hGt : ContDiffAt ℝ 1 coreReflectionTime Y := by
    change ContDiffAt ℝ 1 (fun X => reflectionReturnTime (F X) + coreRadiusReturnTime X) Y
    exact ((hrt.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).comp Y hF).add ht
  have hG : ContDiffAt ℝ 1 G Y := by
    change ContDiffAt ℝ 1 (reflectionReturnState ∘ F) Y
    exact (hrf.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).comp Y hF
  have hzb : Z 1 + Z 2 ≤ Y 1 + Y 2 := add_le_add (hzle 0) (hzle 1)
  have hscale {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : R * a / Z 0 ≤ 2 * R * b / Y 0 := by
    calc
      _ ≤ R * a / (Y 0 / 2) := div_le_div_of_nonneg_left (mul_nonneg hR.le ha) (half_pos hk0) hZrange.1
      _ = 2 * R * a / Y 0 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hab (by positivity)) hk0.le
  have hconn : |G Y 0 - (Z 0 - 2)| ≤ 2 * R * (Y 1 + Y 2) / Y 0 :=
    hrval.trans (hscale (add_nonneg (hzpos 0).le (hzpos 1).le) hzb)
  have hsum : |Z 0 - Y 0| + |G Y 0 - (Z 0 - 2)| ≤ C * (Y 1 + Y 2) / Y 0 :=
    (add_le_add hval hconn).trans_eq (by dsimp [C]; ring)
  have htotalErr : |G Y 0 - (Y 0 - 2)| ≤ C * (Y 1 + Y 2) / Y 0 := by
    have heq : G Y 0 - (Y 0 - 2) = (Z 0 - Y 0) + (G Y 0 - (Z 0 - 2)) := by ring
    rw [heq]
    exact (abs_add_le _ _).trans hsum
  have hhalf : C * (Y 1 + Y 2) / Y 0 ≤ 1 / 2 := by
    calc
      _ ≤ C * ε / Y 0 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbε hC.le) hk0.le
      _ ≤ C * ε / 2 := div_le_div_of_nonneg_left (mul_nonneg hC.le hε.le) (by norm_num) hk
      _ ≤ _ := div_le_div_of_nonneg_right hCε (by norm_num)
  have hdrop : 3 / 2 ≤ Y 0 - G Y 0 ∧ Y 0 - G Y 0 ≤ 5 / 2 := by
    have HH := abs_le.mp (htotalErr.trans hhalf)
    constructor <;> linarith only [HH.1, HH.2]
  refine ⟨htotal, horbit, hGt, hG, hsum, htotalErr, hdrop, ?_, ?_, ?_⟩
  · intro i
    exact ⟨hzpos i, (hrwall i).1, (hrwall i).2, (hwall i).2.2⟩
  · intro hnext i
    exact ((hrwall i).2.trans ((hzle i).trans (hin i))).trans
      (div_le_div_of_nonneg_left hε.le (by linarith only [hnext]) (by linarith only [hdrop.1]))
  · intro v hv0 hv1 hv2 d
    let w := fderiv ℝ F Y v
    obtain ⟨hm, hl, hcone⟩ := hdiff v hv0 hv1 hv2
    have hw0 : 0 < w 0 := by linarith only [hm.1]
    have Htransport := positive_cone_transport (fderiv ℝ reflectionReturnState Z) hw0 hcone (by
      intro z hz0 hz
      obtain ⟨hmargin, _, hlog, hzc⟩ := hrdiff z hz0 (hz 0) (hz 1)
      exact ⟨by linarith only [hmargin], hlog, hzc⟩)
    have hd : d = fderiv ℝ reflectionReturnState Z w := by
      change fderiv ℝ (reflectionReturnState ∘ F) Y v = _
      rw [fderiv_comp Y (hrf.differentiableAt (by norm_num)) (hF.differentiableAt (by norm_num)),
        ContinuousLinearMap.comp_apply]
    rw [hd]
    refine ⟨Htransport.1, Htransport.2.1.trans ?_, Htransport.2.2⟩
    have hrlog := hscale (Real.sqrt_nonneg (Z 1 + Z 2)) (Real.sqrt_le_sqrt hzb)
    exact (add_le_add hl hrlog).trans_eq (by dsimp [C]; ring)
