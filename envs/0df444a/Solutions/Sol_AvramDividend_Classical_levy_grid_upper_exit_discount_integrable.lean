-- Prove2me | solution 1 for AvramDividend.Classical.levy_grid_upper_exit_discount_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T10:45:05.695063+00:00
-- url     : https://prove2.me/submissions/ed12b9ad-e022-4b4f-a3ba-b81d6fe1811d

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_grid_stopped_reserve_time_measurable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The positive-discount finite-grid upper-exit payoff is integrable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → NNReal) (H : Filtration ℕ mΩ)
    (hH : ∀ k, H k = 𝓕 (clock k))
    (lower upper : ℝ) (m : ℕ) (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (X.X (clock k) ω - upper)
        (lower - X.X (clock k) ω)) (Ioi (0 : ℝ)) 0 m ω)
    (q : ℝ) (hq : 0 ≤ q) :
    Integrable
      ({ω : Ω | upper < X.X (clock (K ω)) ω}.indicator
        (fun ω => Real.exp (-((clock (K ω)) : ℝ) * q))) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  let Y : Ω → ℝ := fun ω => X.X (clock (K ω)) ω
  let D : Ω → ℝ := fun ω => ((clock (K ω)) : ℝ) * q
  let S : Set Ω := {ω | upper < Y ω}
  have hm := chat03_grid_stopped_reserve_time_measurable
    X clock H hH lower upper m K hK
  have hY : Measurable Y := hm.1
  have hT : Measurable (fun ω => ((clock (K ω)) : ℝ)) := hm.2
  have hD : Measurable D := hT.mul_const q
  have hS : MeasurableSet S := by
    change MeasurableSet (Y ⁻¹' Ioi upper)
    exact measurableSet_Ioi.preimage hY
  have he : Measurable (fun ω => Real.exp (-D ω)) :=
    Real.measurable_exp.comp hD.neg
  have hmeas : Measurable
      (S.indicator (fun ω => Real.exp (-D ω))) :=
    he.indicator hS
  have hbound : ∀ ω : Ω,
      ‖S.indicator (fun z => Real.exp (-D z)) ω‖ ≤ (1 : ℝ) := by
    intro ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have hnonneg : 0 ≤ D ω := by
        dsimp [D]
        exact mul_nonneg (by positivity) hq
      have hh := Real.exp_le_exp.mpr (neg_nonpos.mpr hnonneg)
      simpa only [Real.exp_zero] using hh
    · simp [Set.indicator, hω]
  have hI : Integrable
      (S.indicator (fun ω => Real.exp (-D ω))) P :=
    Integrable.of_bound hmeas.aestronglyMeasurable 1
      (Filter.Eventually.of_forall hbound)
  simpa only [S, D, Y, neg_mul] using hI
