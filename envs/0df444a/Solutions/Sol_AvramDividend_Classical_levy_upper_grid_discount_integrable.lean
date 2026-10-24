-- Prove2me | solution 1 for AvramDividend.Classical.levy_upper_grid_discount_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T07:22:55.318394+00:00
-- url     : https://prove2.me/submissions/ffd946dd-b6aa-418e-988a-4cf9c382d00b

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_upper_grid_stopped_reserve_time_measurable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → ℝ≥0) (H : Filtration ℕ mΩ)
    (hH : ∀ k, H k = 𝓕 (clock k))
    (z : ℝ) (m : ℕ) (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => X.X (clock k) ω) (Ioi z) 0 m ω)
    (q : ℝ) (hq : 0 ≤ q) :
    Integrable ({ω : Ω | z < X.X (clock (K ω)) ω}.indicator
      (fun ω => Real.exp (-((clock (K ω)) : ℝ) * q))) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  let Y : Ω → ℝ := fun ω => X.X (clock (K ω)) ω
  let D : Ω → ℝ := fun ω => ((clock (K ω)) : ℝ) * q
  let S : Set Ω := {ω | z < Y ω}
  have hm := levy_upper_grid_stopped_reserve_time_measurable
    X clock H hH z m K hK
  have hY : Measurable Y := hm.1
  have hT : Measurable (fun ω => ((clock (K ω)) : ℝ)) := hm.2
  have hD : Measurable D := hT.mul_const q
  have hS : MeasurableSet S := by
    change MeasurableSet (Y ⁻¹' Ioi z)
    exact measurableSet_Ioi.preimage hY
  have he : Measurable (fun ω => Real.exp (-D ω)) :=
    Real.measurable_exp.comp hD.neg
  have hmeas : Measurable
      (S.indicator (fun ω => Real.exp (-D ω))) :=
    he.indicator hS
  have hbound : ∀ ω : Ω,
      ‖S.indicator (fun y => Real.exp (-D y)) ω‖ ≤ (1 : ℝ) := by
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
