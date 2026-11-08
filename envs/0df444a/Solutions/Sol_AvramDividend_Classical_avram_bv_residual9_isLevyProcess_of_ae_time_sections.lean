-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_isLevyProcess_of_ae_time_sections
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T21:33:44.242614+00:00
-- url     : https://prove2.me/submissions/1da80379-33c2-4339-b3cb-5b9cb4218012

import Mathlib.Probability.Independence.Basic
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_ProbabilityTheory_increment_apply
import Theorems.Thm_ProbabilityTheory_measurable_increment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (X Y : ℝ≥0 → Ω → ℝ) (hX : IsLevyProcess X P)
    (hY0 : ∀ ω, Y 0 ω = 0)
    (hYm : ∀ t, Measurable (Y t))
    (hYcad : ∀ᵐ ω ∂P, IsCadlag (fun t : ℝ≥0 => Y t ω))
    (hYX : ∀ t, Y t =ᵐ[P] X t) :
    IsLevyProcess Y P where
  start_zero := by
    funext ω
    exact hY0 ω
  indep_increments := by
    intro n τ hτmono
    have heq : ∀ k : Fin n,
        increment X (τ k.castSucc) (τ k.succ) =ᵐ[P]
          increment Y (τ k.castSucc) (τ k.succ) := by
      intro k
      filter_upwards [(hYX (τ k.castSucc)).symm,
        (hYX (τ k.succ)).symm] with ω ha hb
      simp only [increment_apply]
      rw [ha, hb]
    exact (iIndepFun_congr heq).mp (hX.indep_increments n τ hτmono)
  stationary_increments := by
    intro s h
    have hint : ∀ p q : ℝ≥0,
        AEMeasurable (increment Y p q) P :=
      fun p q => (measurable_increment (hYm p) (hYm q)).aemeasurable
    have heq : ∀ p q : ℝ≥0,
        increment Y p q =ᵐ[P] increment X p q := by
      intro p q
      filter_upwards [hYX p, hYX q] with ω ha hb
      simp only [increment_apply]
      rw [ha, hb]
    exact ((IdentDistrib.of_ae_eq (hint s (s + h))
      (heq s (s + h))).trans (hX.stationary_increments s h)).trans
      (IdentDistrib.of_ae_eq (hint 0 h) (heq 0 h)).symm
  cadlag_ae := hYcad
