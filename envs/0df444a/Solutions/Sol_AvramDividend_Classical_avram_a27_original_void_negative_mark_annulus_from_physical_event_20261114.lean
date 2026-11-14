-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_void_negative_mark_annulus_from_physical_event_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:49:00.0192+00:00
-- url     : https://prove2.me/submissions/a0ab7d5d-1fc3-4d1f-8d1a-29cb014e459c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a26_original_all_horizons_no_tiny_negative_marks_eventually_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a27_restricted_mark_pushforward_disjoint_support_zero_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Source absence of omitted negative marks implies exactly zero physical marked-jump measure on every shrinking annulus. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hMark : ∀ ω : Ω,
      Measurable (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      ∃ N : ℕ, ∀ n ≥ N,
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ Ioo (-(1 / ((n : ℝ) + 1))) (0 : ℝ)) = 0 := by
  filter_upwards [
    avram_a26_original_all_horizons_no_tiny_negative_marks_eventually_20261114
      X hFinite] with ω hω
  intro T
  obtain ⟨N, hN⟩ := hω T
  refine ⟨N, ?_⟩
  intro n hn
  let j : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  let S : Set ℝ≥0 := {u | 0 < u ∧ j u ≠ 0}
  let E : Set (ℝ≥0 × ℝ) :=
    Ioc 0 T ×ˢ Ioo (-(1 / ((n : ℝ) + 1))) (0 : ℝ)
  have hE : MeasurableSet E :=
    measurableSet_Ioc.prod measurableSet_Ioo
  have hNo : ∀ u ∈ S, (u, j u) ∉ E := by
    intro u hu hMem
    have hTiny := hN n hn u hu.1 hMem.1.2
    exact hTiny hMem.2
  simpa only [S, E, j] using
    (avram_a27_restricted_mark_pushforward_disjoint_support_zero_20261114
      Measure.count S (fun u : ℝ≥0 => (u, j u)) (hMark ω) E hE hNo)
