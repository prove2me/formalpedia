-- Prove2me | solution 1 for BianchiIX.exists_coreRadiusReturn_estimates
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T04:53:51.444198+00:00
-- url     : https://prove2.me/submissions/60efb20b-2da0-447a-bd89-f05b7da97eb2

import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Theorems.Thm_BianchiIX_abs_log_le_twice_error
import Theorems.Thm_BianchiIX_exists_coreRadiusReturn_invariant_cone
import Theorems.Thm_BianchiIX_exists_coreRadiusReturn_phase_bounds
import Theorems.Thm_BianchiIX_exists_coreRadiusReturn_uniform_contraction
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

noncomputable section
open BianchiIX


/-- Phase drift, logarithmic distortion, wall contraction and cone preservation share one actual core domain. -/
theorem solution :
    ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), c ≤ 1 / 2 ∧
      ∀ Y : CoreAngleState, 2 ≤ Y 0 →
        (0 ≤ Y 1 ∧ Y 1 ≤ ε / Y 0) → (0 ≤ Y 2 ∧ Y 2 ≤ ε / Y 0) →
        let F := coreReturnState coreRadiusReturnTime
        coreRadiusReturnValid Y ∧ ContDiffAt ℝ 1 coreRadiusReturnTime Y ∧ ContDiffAt ℝ 1 F Y ∧
          |F Y 0 - Y 0| ≤ C * (Y 1 + Y 2) / Y 0 ∧
          (∀ i : Fin 2, 0 ≤ F Y i.succ ∧ (0 < F Y i.succ ↔ 0 < Y i.succ) ∧
            F Y i.succ ≤ Real.exp (-c / Y 0) * Y i.succ) ∧
          ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
            let d := fderiv ℝ F Y v
            (3 / 4 ≤ d 0 ∧ d 0 ≤ 5 / 4) ∧
              |Real.log (d 0)| ≤ C * Real.sqrt (Y 1 + Y 2) / Y 0 ∧
              ∀ i : Fin 2, |d i.succ| ≤ Real.sqrt (F Y i.succ) * d 0 := by
  obtain ⟨εp, hεp, _, C, hC, Hp⟩ := exists_coreRadiusReturn_phase_bounds
  obtain ⟨εc, hεc, _, Hc⟩ := exists_coreRadiusReturn_invariant_cone
  obtain ⟨εd, hεd, hεη, c, hc, hcmax, Hd⟩ := exists_coreRadiusReturn_uniform_contraction
  let δ := 1 / (4 * C)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hCδ : C * δ = 1 / 4 := by dsimp [δ]; field_simp
  let ε := min εd (min εp (min εc (δ ^ 2)))
  have hε : 0 < ε := lt_min hεd (lt_min hεp (lt_min hεc (sq_pos_of_pos hδ)))
  have hεd' : ε ≤ εd := min_le_left _ _
  have hεp' : ε ≤ εp := (min_le_right _ _).trans (min_le_left _ _)
  have hεc' : ε ≤ εc := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεδ : ε ≤ δ ^ 2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ε, hε, hεd'.trans hεη, 2 * C, by positivity, c, hc, hcmax, ?_⟩
  intro Y hk hu hw F
  have hk0 : 0 < Y 0 := by linarith only [hk]
  have hscale {r : ℝ} (hr : ε ≤ r) : ε / Y 0 ≤ r / Y 0 :=
    div_le_div_of_nonneg_right hr hk0.le
  obtain ⟨hvalid, ht, hF, hwalls⟩ := Hd Y hk
    ⟨hu.1, hu.2.trans (hscale hεd')⟩ ⟨hw.1, hw.2.trans (hscale hεd')⟩
  obtain ⟨_, _, hval, hderiv⟩ := Hp Y hk
    ⟨hu.1, hu.2.trans (hscale hεp')⟩ ⟨hw.1, hw.2.trans (hscale hεp')⟩
  have hcone := Hc Y hk
    ⟨hu.1, hu.2.trans (hscale hεc')⟩ ⟨hw.1, hw.2.trans (hscale hεc')⟩
  have hb : 0 ≤ Y 1 + Y 2 := add_nonneg hu.1 hw.1
  have hbε : Y 1 + Y 2 ≤ ε := by
    nlinarith only [(le_div_iff₀ hk0).mp hu.2, (le_div_iff₀ hk0).mp hw.2,
      mul_le_mul_of_nonneg_right hk hu.1, mul_le_mul_of_nonneg_right hk hw.1]
  have hs : Real.sqrt (Y 1 + Y 2) ≤ δ := Real.sqrt_le_iff.mpr ⟨hδ.le, hbε.trans hεδ⟩
  have he : C * Real.sqrt (Y 1 + Y 2) / Y 0 ≤ 1 / 4 := by
    calc
      _ ≤ C * Real.sqrt (Y 1 + Y 2) := div_le_self (by positivity) (by linarith only [hk])
      _ ≤ C * δ := mul_le_mul_of_nonneg_left hs hC.le
      _ = _ := hCδ
  refine ⟨hvalid, ht, hF, hval.trans ?_, hwalls, ?_⟩
  · apply div_le_div_of_nonneg_right _ hk0.le
    exact mul_le_mul_of_nonneg_right (by linarith only [hC] : C ≤ 2 * C) hb
  · intro v hv0 hv1 hv2 d
    have herr := hderiv v hv0 hv1 hv2
    have hmargin := herr.trans he
    refine ⟨⟨by linarith only [(abs_le.mp hmargin).1],
      by linarith only [(abs_le.mp hmargin).2]⟩, ?_, (hcone v hv0 hv1 hv2).2⟩
    exact (abs_log_le_twice_error he herr).trans_eq (by ring)
