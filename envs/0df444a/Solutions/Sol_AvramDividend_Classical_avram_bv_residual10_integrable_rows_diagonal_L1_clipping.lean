-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_integrable_rows_diagonal_L1_clipping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:12:29.663104+00:00
-- url     : https://prove2.me/submissions/cbc29730-5d45-46b6-9b7d-0b05a932f039

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_integrable_original_grid_localisation_tail

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A row-dependent deterministic cutoff makes the L1 localisation error
smaller than an explicit vanishing target, for integrable original row data. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (a : ℕ → Ω → ℕ → ℝ)
    (ha : ∀ n i, Measurable (fun ω => a n ω i))
    (f : ℕ → Ω → ℝ)
    (hfm : ∀ n, Measurable (f n))
    (hf : ∀ n, Integrable (f n) P) :
    ∃ K : ℕ → ℕ, ∀ n : ℕ,
      (∫ ω : Ω,
        if ω ∈ {z : Ω | ∀ i ∈ Finset.range (n + 1),
          abs (a n z i) ≤ (K n : ℝ)} then (0 : ℝ)
          else abs (f n ω) ∂P) < 1 / ((n : ℝ) + 1) := by
  have hselect (n : ℕ) : ∃ k : ℕ,
      (∫ ω : Ω,
        if ω ∈ {z : Ω | ∀ i ∈ Finset.range (n + 1),
          abs (a n z i) ≤ (k : ℝ)} then (0 : ℝ)
          else abs (f n ω) ∂P) < 1 / ((n : ℝ) + 1) := by
    have hlim := avram_bv_residual10_integrable_original_grid_localisation_tail
      n (a n) (ha n) (f n) (hfm n) (hf n)
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact (hlim.eventually (eventually_lt_nhds hpos)).exists
  choose K hK using hselect
  exact ⟨K, hK⟩
