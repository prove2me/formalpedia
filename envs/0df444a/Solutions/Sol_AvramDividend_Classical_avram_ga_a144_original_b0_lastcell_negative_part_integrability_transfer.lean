-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a144_original_b0_lastcell_negative_part_integrability_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:40:31.118333+00:00
-- url     : https://prove2.me/submissions/47f7cff0-a12f-4d30-b518-ff46b7128cac

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

/-- Exact original Gaussian m versus m+1 terminal correction transfers positive root integrability from the proved extra-cell result using only the negative part of the omitted last source value. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (U S Last : ℕ → Ω → ℝ)
    (hDiff : ∀ m ω, U m ω = S m ω - Last m ω)
    (hMeas : ∀ m, AEStronglyMeasurable (fun ω => max (U m ω) 0) P)
    (hSI : ∀ m, Integrable (fun ω => max (S m ω) 0) P)
    (hLast : ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => max (-Last m ω) 0) P) :
    ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => max (U m ω) 0) P := by
  obtain ⟨k, hL⟩ := hLast
  refine ⟨k, ?_⟩
  intro m hm
  have hp (ω : Ω) :
      max (U m ω) 0 ≤ max (S m ω) 0 + max (-Last m ω) 0 := by
    rw [hDiff m ω]
    apply max_le
    · linarith [le_max_left (S m ω) 0,
        le_max_left (-Last m ω) 0]
    · linarith [le_max_right (S m ω) 0,
        le_max_right (-Last m ω) 0]
  have hBound : ∀ᵐ ω ∂P,
      ‖max (U m ω) 0‖ ≤ max (S m ω) 0 + max (-Last m ω) 0 := by
    filter_upwards [] with ω
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (le_max_right (U m ω) 0)] using hp ω
  exact Integrable.mono'
    ((hSI m).add (hL m hm)) (hMeas m) hBound
