-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bt_new_ae_instant_ruin_of_strict_horizon_null
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T23:24:23.866992+00:00
-- url     : https://prove2.me/submissions/eff44b01-040c-497e-82a1-83365802b9bf

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (τ : Ω → ℝ≥0∞)
    (hNull : ∀ t : ℝ≥0∞, 0 < t →
      P {ω : Ω | t < τ ω} = 0) :
    ∀ᵐ ω ∂P, τ ω = 0 := by
  rw [ae_iff]
  have hsub : {ω | ¬ τ ω = 0} ⊆ ⋃ n : ℕ, {ω | ((n : ℝ≥0∞))⁻¹ < τ ω} := by
    intro ω hω
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hω
    exact mem_iUnion.2 ⟨n, hn⟩
  refine measure_mono_null hsub (measure_iUnion_null fun n => hNull _ ?_)
  exact ENNReal.inv_pos.2 (ENNReal.natCast_ne_top n)
