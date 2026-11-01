-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_original_marked_l2_tail_from_levy_envelope_without_sfinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:50:44.336833+00:00
-- url     : https://prove2.me/submissions/08de07d7-f1b3-4819-91a4-d72ff5ebdfe1

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_null_zero_energy_canonical_mark_band_exhaustion
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_stopped_marked_l2_product_band_exhaustion

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem solution
    {A E : Type*} [MeasurableSpace A] [MeasurableSpace E]
    (μ : Measure A) [IsFiniteMeasure μ] (ν : Measure E)
    (g : E → ℝ≥0∞) (hg : Measurable g)
    (henergy : ∫⁻ z, g z ∂ν < ∞)
    (hzero_null : ν {z | g z = 0} = 0)
    (F : A × E → ℝ≥0∞) (hF : Measurable F)
    (C : ℝ≥0∞) (hC : C < ∞)
    (hdom : ∀ p, F p ≤ C * g p.2) :
    let B : ℕ → Set E := fun n =>
      {z | (n : ℝ≥0∞)⁻¹ ≤ g z} ∪ {z | g z = 0}
    Tendsto (fun n : ℕ =>
      ∫⁻ p in Set.univ ×ˢ (B n)ᶜ, F p ∂μ.prod ν)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
  let B : ℕ → Set E := fun n =>
    {z | (n : ℝ≥0∞)⁻¹ ≤ g z} ∪ {z | g z = 0}
  obtain ⟨hm, hfin, hmono, hcover⟩ :=
    AvramDividend.Classical.avram_wave4_p1_null_zero_energy_canonical_mark_band_exhaustion
      ν g hg henergy hzero_null
  letI : SigmaFinite ν := ⟨⟨{
    set := B
    set_mem := fun n => Set.mem_univ (B n)
    finite := hfin
    spanning := hcover
  }⟩⟩
  haveI : SFinite ν := inferInstance
  exact AvramDividend.Classical.avram_wave4_p1_stopped_marked_l2_product_band_exhaustion
    μ ν g hg henergy F hF C hC hdom B hm hfin hmono hcover
