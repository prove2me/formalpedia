-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_measurable_random_stopped_prefix_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T19:09:07.526947+00:00
-- url     : https://prove2.me/submissions/0492bf43-0578-41e2-b139-68e14b486d48

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_stopped_index_masked_AE_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_stopped_prefix_eq_masked_finite_grid
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped BigOperators

/-- Exact random stopped physical-grid prefixes of measurable cell terms
remain almost-everywhere strongly measurable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (N : ℕ) (k : Ω → ℕ) (hk : Measurable k)
    (hBound : ∀ ω, k ω ≤ N)
    (f : ℕ → Ω → ℝ)
    (hf : ∀ i, AEStronglyMeasurable (f i) P) :
    AEStronglyMeasurable (fun ω =>
      ∑ i ∈ Finset.range (k ω), f i ω) P := by
  have hmask : AEStronglyMeasurable (fun ω =>
      ∑ i ∈ Finset.range N, if i < k ω then f i ω else 0) P :=
    avram_bv_error7_stopped_index_masked_AE_measurable N k hk f hf
  have hEq : (fun ω => ∑ i ∈ Finset.range N,
      if i < k ω then f i ω else 0) =
      (fun ω => ∑ i ∈ Finset.range (k ω), f i ω) := by
    funext ω
    exact avram_bv_error7_stopped_prefix_eq_masked_finite_grid
      N (k ω) (hBound ω) (fun i => f i ω)
  rw [hEq] at hmask
  exact hmask
