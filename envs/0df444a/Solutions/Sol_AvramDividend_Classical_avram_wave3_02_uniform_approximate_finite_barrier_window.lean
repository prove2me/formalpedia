-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_uniform_approximate_finite_barrier_window
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T22:17:50.827084+00:00
-- url     : https://prove2.me/submissions/b967aab2-d716-462f-b15a-c372a9553e8a

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.OrderClosed
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_uniform_bounded_reserves_high_barrier_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Every positive error tolerance gives one bounded cap search window
uniform across all nonnegative initial reserves up to a common limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x : ℝ, 0 ≤ x → x ≤ R →
      (⨆ a : ℝ, ⨆ (_ : 0 ≤ a),
        dividendValue X q x (barrierStrategy X x a)) ≤
      (⨆ a : ℝ, ⨆ (_ : 0 ≤ a ∧ a ≤ A),
        dividendValue X q x (barrierStrategy X x a)) ⊔ ENNReal.ofReal ε := by
  have hlim :=
    avram_wave3_02_uniform_bounded_reserves_high_barrier_zero
      X hX q hq W hW R hR
  have hevent : ∀ᶠ a : ℝ in atTop,
      (⨆ x : ℝ, ⨆ (_ : 0 ≤ x ∧ x ≤ R),
        dividendValue X q x (barrierStrategy X x a)) <
      ENNReal.ofReal ε :=
    Filter.Tendsto.eventually_lt_const (ENNReal.ofReal_pos.mpr hε) hlim
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.1 hevent
  let B : ℝ := max A 0
  have hB : 0 ≤ B := le_max_right _ _
  refine ⟨B, hB, ?_⟩
  intro x hx hxR
  refine iSup_le fun a => ?_
  refine iSup_le fun ha => ?_
  by_cases hab : a ≤ B
  · have hIn : dividendValue X q x (barrierStrategy X x a) ≤
        (⨆ t : ℝ, ⨆ (_ : 0 ≤ t ∧ t ≤ B),
          dividendValue X q x (barrierStrategy X x t)) :=
      le_iSup_of_le a (le_iSup_of_le ⟨ha, hab⟩ (le_refl _))
    exact le_sup_of_le_left hIn
  · have hAa : A ≤ a :=
      (le_max_left A 0).trans (le_of_lt (lt_of_not_ge hab))
    have hIn : dividendValue X q x (barrierStrategy X x a) ≤
        (⨆ y : ℝ, ⨆ (_ : 0 ≤ y ∧ y ≤ R),
          dividendValue X q y (barrierStrategy X y a)) :=
      le_iSup_of_le x (le_iSup_of_le ⟨hx, hxR⟩ (le_refl _))
    have hSmall : dividendValue X q x (barrierStrategy X x a) ≤
        ENNReal.ofReal ε := hIn.trans (le_of_lt (hA a hAa))
    exact le_sup_of_le_right hSmall
