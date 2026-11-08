-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_original_rowwise_ae_eventual_clipping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:40:50.865871+00:00
-- url     : https://prove2.me/submissions/06eb13e0-29ba-4a4b-b9fc-84b4321246c8

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_rowwise_probability_diagonal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Summably small exceptions to the original physical-row coefficient bounds
are absent eventually almost surely, by the first Borel-Cantelli lemma. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P]
    (a : ℕ → Ω → ℕ → ℝ)
    (ha : ∀ n i, Measurable (fun ω => a n ω i))
    (ε : ℕ → ℝ≥0∞) (hεpos : ∀ n, 0 < ε n)
    (hεlim : Tendsto ε atTop (𝓝 (0 : ℝ≥0∞)))
    (hεsum : (∑' n, ε n) ≠ ⊤) :
    ∃ K : ℕ → ℕ, ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      ∀ i ∈ Finset.range (n + 1), abs (a n ω i) ≤ (K n : ℝ) := by
  obtain ⟨K, hK, _⟩ :=
    avram_bv_residual10_original_rowwise_probability_diagonal
      (P := P) a ha ε hεpos hεlim
  let A : ℕ → Set Ω := fun n =>
    {ω | ∀ i ∈ Finset.range (n + 1), abs (a n ω i) ≤ (K n : ℝ)}
  have hsum : (∑' n, P ((A n)ᶜ)) ≠ ⊤ := by
    have hle : (∑' n, P ((A n)ᶜ)) ≤ ∑' n, ε n :=
      ENNReal.tsum_le_tsum (fun n => le_of_lt (hK n))
    exact (lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hεsum)).ne
  have hBC : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∉ (A n)ᶜ :=
    ae_eventually_notMem hsum
  refine ⟨K, ?_⟩
  filter_upwards [hBC] with ω hω
  filter_upwards [hω] with n hn
  simpa [A] using hn
