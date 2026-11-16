-- Prove2me | solution 1 for AvramDividend.Classical.avram_b27_marked_large_only_count_small_band_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:26:21.030936+00:00
-- url     : https://prove2.me/submissions/65515c97-c924-4408-bb81-4b973142474b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (μ : Measure ℝ≥0) (f : ℝ≥0 → ℝ≥0 × ℝ)
    (hf : AEMeasurable f μ)
    (hLarge : ∀ u : ℝ≥0, (f u).2 = 0 ∨ (f u).2 ≤ -1)
    (n : ℕ) (t : ℝ≥0) :
    (∫ p in (Ioc (0 : ℝ≥0) t ×ˢ
        Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))),
      p.2 ∂(μ.map f)) = 0 := by
  let B : Set (ℝ≥0 × ℝ) :=
    Ioc (0 : ℝ≥0) t ×ˢ Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
  have hn : -(1 / ((n : ℝ) + 1)) < 0 := by
    have hp : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    linarith
  have hPre : f ⁻¹' B = ∅ := by
    ext u
    simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
    intro h
    have hmark : (f u).2 ∈ Ioc (-1 : ℝ)
        (-(1 / ((n : ℝ) + 1))) := h.2
    rcases hmark with ⟨hlo, hhi⟩
    rcases hLarge u with hz | hle
    · linarith
    · linarith
  have hB : MeasurableSet B := measurableSet_Ioc.prod measurableSet_Ioc
  have hZero : (μ.map f) B = 0 := by
    rw [Measure.map_apply_of_aemeasurable hf hB, hPre]
    simp
  have hRestrict : (μ.map f).restrict B = 0 :=
    Measure.restrict_eq_zero.mpr hZero
  change (∫ p, p.2 ∂((μ.map f).restrict B)) = 0
  rw [hRestrict]
  simp
