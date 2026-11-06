-- Prove2me | solution 1 for BianchiIX.connectionReturn_fixed_clock_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T10:31:11.94808+00:00
-- url     : https://prove2.me/submissions/f6008649-42af-41f1-a90e-edc49e436ea9

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_ConnectionClockDifferential
import Definitions.Def_BianchiIX_Analysis_ConnectionLogCoordinates
import Definitions.Def_BianchiIX_Dynamics_ConnectionRegion
import Definitions.Def_BianchiIX_Analysis_ConnectionWeightedVariation
import Definitions.Def_BianchiIX_Analysis_ConnectionFeedbackBounds
import Definitions.Def_BianchiIX_Dynamics_ConnectionExistence
import Definitions.Def_BianchiIX_Dynamics_ConnectionLogFlowVariation
import Definitions.Def_BianchiIX_Dynamics_ConnectionEvents
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturn
import Theorems.Thm_BianchiIX_connectionLog_actual_growing_variation_bounds
import Theorems.Thm_BianchiIX_connectionLog_actual_radial_variation_bounds
import Theorems.Thm_BianchiIX_connectionLog_actual_strong_variation_bounds
import Theorems.Thm_BianchiIX_connectionReturn_regular
import Theorems.Thm_BianchiIX_exists_connectionReturn_log_clock
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Module
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Order.ProjIcc

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connection_denom_bound {m u v w : ℝ}
    (hu : 0 ≤ u ∧ u ≤ 1 / 10000) (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    3 + m ^ 2 - 4 * u ≤ projectiveDenom (-m) u v w ∧ 0 < projectiveDenom (-m) u v w := by
  have H : 3 + m ^ 2 - 4 * u ≤ projectiveDenom (-m) u v w := by
    dsimp [projectiveDenom, curvature]
    nlinarith only [mul_le_mul_of_nonneg_left hv.2 hu.1,
      mul_le_mul_of_nonneg_left hw.2 hu.1, sq_nonneg u, sq_nonneg (v - w)]
  exact ⟨H, by nlinarith only [H, hu.2, sq_nonneg m]⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.connection_entry_denom_pos {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    0 < projectiveStateDenom (connectionEntry (p 0) (p 1) (p 2)) := by
  have hu' : 0 ≤ p 1 ∧ p 1 ≤ 1 / 10000 :=
    ⟨hu.1, hu.2.trans (div_le_self (by norm_num) (by linarith only [hμ]))⟩
  exact (connection_denom_bound (m := p 0) (v := 1) hu' (by norm_num)
    ⟨hw.1.le, hw.2.trans (by norm_num)⟩).2

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.connectionReturn_growing_component {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    connectionReturnState p 3 = 1 ∧ ∀ v : ConnectionParameters, fderiv ℝ connectionReturnState p v 3 = 0 := by
  have H := connectionReturn_regular hμ hu hw
  have heq : (fun q => connectionReturnState q 3) =ᶠ[𝓝 p] (fun _ => (1 : ℝ)) := by
    filter_upwards [H.2.2.2.2.2] with q hq
    exact hq.1.1.2.2
  have hd := (hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) p).congr_of_eventuallyEq heq
  have hc := (hasFDerivAt_apply (𝕜 := ℝ) (3 : Fin 4) (connectionReturnState p)).comp p
    ((H.2.2.1.differentiableAt (by norm_num)).hasFDerivAt)
  refine ⟨heq.self_of_nhds, ?_⟩
  intro v
  have hlinear := hc.unique hd
  exact congrArg (fun L : ConnectionParameters →L[ℝ] ℝ => L v) hlinear

end
end

/-- Fixed-relative-clock responses at the canonical arrival, with all orbit hypotheses discharged. -/
theorem solution {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 < p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    let μ := p 0
    let u := p 1
    let w := p 2
    let L := -Real.log w
    let y := connectionEntry μ u w
    let D := connectionLogFlowVariation y 0 (connectionReturnTime p)
    (|D ![-1, 0, 0, 0] 0| ≤ 16 / 15 ∧
      |D ![-1, 0, 0, 0] 0 - connectionLogTangent y ![-1, 0, 0, 0] 0| ≤
        (16 / 15) * connectionPhaseFeedbackBudget μ u w ∧
      ‖connectionWeightedTangent μ (D ![-1, 0, 0, 0])‖ ≤ (2048 / 15) * L) ∧
    (|D ![0, 1, 0, 0] 0| ≤ 70 / μ ∧
      |D ![0, 1, 0, 0] 1| ≤ 1 / u + 256 + 8960 * L / μ ∧
      |D ![0, 1, 0, 0] 2| ≤ (256 + 8960 * L / μ) / μ ^ 2) ∧
    (|D ![0, 0, 0, 1] 0| ≤ 8000 * (u + w) / μ ∧
      |D ![0, 0, 0, 1] 1| ≤ 32 + 12800 * u + 96 / (μ * w) + 1024000 * L * (u + w) / μ ∧
      |D ![0, 0, 0, 1] 2| ≤ (12800 * u + 64 / (μ * w) + 1024000 * L * (u + w) / μ) / μ ^ 2) := by
  intro μ u w L y D
  obtain ⟨hL, q, hq0, hqL, H⟩ := exists_connectionReturn_log_clock hμ hu hw
  change q L = connectionReturnTime p at hqL
  have hden := connection_entry_denom_pos hμ ⟨hu.1.le, hu.2⟩ hw
  have hdom z hz := (H z hz).1
  have hchart z hz := (H z hz).2.1
  have hm z hz := (H z hz).2.2.1.1
  have hU z hz := And.intro (H z hz).2.2.2.1 (H z hz).2.2.1.2.1.2
  have hV z hz := And.intro (H z hz).2.2.2.2.1 (H z hz).2.2.1.2.2.1.2
  have hW z hz := And.intro (H z hz).2.2.2.2.2.1 (H z hz).2.2.1.2.2.2.2
  have hq z hz := (H z hz).2.2.2.2.2.2
  have hentry : y 1 ≤ y 2 := by
    change p 1 ≤ 1
    have hμ0 : 0 < p 0 := by linarith only [hμ]
    have huμ := (le_div_iff₀ hμ0).mp hu.2
    nlinarith only [huμ, hμ, hu.1]
  have hend : L ∈ Icc 0 L := ⟨hL, le_rfl⟩
  have hr := connectionLog_actual_radial_variation_bounds hL hμ hden hdom hchart hm hU hV hW
    hentry hu.2 hw.2 hq hq0 ![-1, 0, 0, 0] (by rfl) (by rfl) (by rfl) L hend
  have hs := connectionLog_actual_strong_variation_bounds hL hμ hden hdom hchart hm hU hV hW
    hentry hu.2 hw.2 hq hq0 L hend
  have hg := connectionLog_actual_growing_variation_bounds hL hμ hden hdom hchart hm hU hV hW
    hentry hu.2 hw.2 hq hq0 L hend
  have hWend : projectiveOriginalFlow y 0 (q L) 3 = 1 := by
    rw [hqL]
    exact (connectionReturn_growing_component hμ ⟨hu.1.le, hu.2⟩ hw).1
  change projectiveOriginalFlow (connectionEntry (p 0) (p 1) (p 2)) 0 (q L) 3 = 1 at hWend
  rw [hWend] at hg
  rw [hqL] at hr hs hg
  refine ⟨?_, ?_, ?_⟩
  · simpa [D, y, μ, u, w, connectionEntry] using hr
  · simpa [D, y, μ, u, w, connectionEntry] using hs
  · simpa [D, y, μ, u, w, connectionEntry] using hg
