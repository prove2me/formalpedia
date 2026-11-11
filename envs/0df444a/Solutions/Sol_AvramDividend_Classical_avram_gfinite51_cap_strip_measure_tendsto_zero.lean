-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite51_cap_strip_measure_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T22:14:37.972481+00:00
-- url     : https://prove2.me/submissions/9b5bbc21-de72-4bf0-8993-5b506ca4bcde

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (Y : Ω → ℝ) (hY : Measurable Y)
    (c : ℝ) (b : ℕ → ℝ) (hbmono : Monotone b)
    (hb : Tendsto b atTop (𝓝 c))
    (hCapNull : μ {ω | c ≤ Y ω} = 0) :
    Tendsto (fun j : ℕ => μ {ω | b j < Y ω})
      atTop (𝓝 (0 : ℝ≥0∞)) := by
  classical
  let s : ℕ → Set Ω := fun j => {ω | b j < Y ω}
  have hs : ∀ j, NullMeasurableSet (s j) μ := by
    intro j
    exact (measurableSet_lt measurable_const hY).nullMeasurableSet
  have hAnti : Antitone s := by
    intro i j hij ω hω
    exact lt_of_le_of_lt (hbmono hij) hω
  have hSub : (⋂ j, s j) ⊆ {ω | c ≤ Y ω} := by
    intro ω hω
    by_contra hωC
    have hyc : Y ω < c := lt_of_not_ge hωC
    obtain ⟨j, hj⟩ := (hb.eventually_const_lt hyc).exists
    have hmem : b j < Y ω := (Set.mem_iInter.mp hω) j
    exact (lt_asymm hj hmem)
  have hNull : μ (⋂ j, s j) = 0 := by
    apply le_antisymm
    · calc
        μ (⋂ j, s j) ≤ μ {ω | c ≤ Y ω} := measure_mono hSub
        _ = 0 := hCapNull
    · exact bot_le
  have hFin : ∃ j, μ (s j) ≠ ⊤ := ⟨0, ne_of_lt (measure_lt_top μ (s 0))⟩
  have hlim := MeasureTheory.tendsto_measure_iInter_atTop hs hAnti hFin
  simpa [s, Function.comp_def, hNull] using hlim
