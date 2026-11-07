-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_18_original_nested_bounded_C2_stop_sequence_covers_its_supremum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:31:15.521578+00:00
-- url     : https://prove2.me/submissions/1df23dc3-a406-45e2-88a2-abf0e1053a35

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_dense_bounded_clock_right_left_uniform_C2
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_nested_bounded_positive_C2_clock_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (r : ℕ → ℝ≥0) (hdense : DenseRange r)
    (lower upper : ℕ → ℝ) (B : ℕ → ℝ≥0)
    (hlower : ∀ n, 0 < lower n)
    (hlo : ∀ n, lower (n + 1) ≤ lower n)
    (hup : ∀ n, upper n ≤ upper (n + 1))
    (hcap : ∀ n, ∀ y ∈ Set.Icc (lower n) (upper n), ENNReal.ofReal y < C)
    (hB : ∀ n, B n ≤ B (n + 1)) :
    let τ : ℕ → Ω → WithTop ℝ≥0 := fun n ω =>
      min (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower n ∨
            upper n < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) (B n : WithTop ℝ≥0)
    let τSup : Ω → WithTop ℝ≥0 := fun ω => ⨆ n, τ n ω
    (∀ n, IsStoppingTime 𝓕.rightCont (τ n)) ∧
      (∀ n ω, τ n ω ≤ τ (n + 1) ω) ∧
      ∀ ω (t : WithTop ℝ≥0), t < τSup ω ↔ ∃ n, t < τ n ω := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact (avram_wave7_18_original_dense_bounded_clock_right_left_uniform_C2
      X x D hD C w hw r (lower n) (upper n)
      (hlower n) (hcap n) hdense (B n)).1
  · intro n ω
    exact (avram_wave7_18_original_nested_bounded_positive_C2_clock_monotone
      X x D hD C w hw r
      (lower n) (upper n) (lower (n + 1)) (upper (n + 1))
      (hlower n) (hlower (n + 1)) (hlo n) (hup n)
      (hcap n) (hcap (n + 1)) hdense
      (B n) (B (n + 1)) (hB n)).2.2 ω
  · intro ω t
    exact lt_iSup_iff
