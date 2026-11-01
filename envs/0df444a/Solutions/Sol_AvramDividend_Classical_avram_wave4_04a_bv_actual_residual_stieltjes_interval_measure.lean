-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_residual_stieltjes_interval_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:13:58.380663+00:00
-- url     : https://prove2.me/submissions/35506e05-c75d-4022-9eb8-9f58dc4d2862

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ F : StieltjesFunction ℝ≥0,
      ∀ s t : ℝ≥0,
        F.measure (Ioc s t) =
          ENNReal.ofReal (((t : ℝ) * X.drift - X.X t ω) -
            ((s : ℝ) * X.drift - X.X s ω)) := by
  filter_upwards [bv_actual_levy_residual_ae_monotone_all_times X hBV] with ω hmono
  let Y : ℝ≥0 → ℝ := fun u => (u : ℝ) * X.drift - X.X u ω
  have hm : Monotone Y := hmono
  have hright : ∀ u : ℝ≥0, Function.rightLim Y u = Y u := by
    intro u
    apply ContinuousWithinAt.rightLim_eq
    have hc : Continuous (fun v : ℝ≥0 => (v : ℝ) * X.drift) :=
      NNReal.continuous_coe.mul continuous_const
    exact hc.continuousWithinAt.sub (X.rightCont ω u)
  let F : StieltjesFunction ℝ≥0 := hm.stieltjesFunction
  have hF : ∀ u : ℝ≥0, F u = Y u := by
    intro u
    change (hm.stieltjesFunction : ℝ≥0 → ℝ) u = Y u
    rw [hm.stieltjesFunction_eq]
    exact hright u
  refine ⟨F, ?_⟩
  intro s t
  rw [StieltjesFunction.measure_Ioc]
  rw [hF t, hF s]
