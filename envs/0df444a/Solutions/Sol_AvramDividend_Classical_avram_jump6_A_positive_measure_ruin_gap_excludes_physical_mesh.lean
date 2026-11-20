-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_positive_measure_ruin_gap_excludes_physical_mesh
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:18:30.579511+00:00
-- url     : https://prove2.me/submissions/6dbee8fa-21ff-49af-bb38-1501362dd111

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_physical_unitmark_ruin_gap_blocks_vanishing_signed_mesh
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Filter AvramDividend.Classical
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Set Ω) (hApos : P.restrict A ≠ 0)
    (y b t : Ω → ℝ)
    (hBounds : ∀ᵐ ω ∂(P.restrict A),
      0 ≤ y ω ∧ y ω ≤ 1 / 5 ∧ b ω ≤ 1 / 100 ∧ t ω ≤ 1 / 10)
    (B E : ℕ → Ω → ℝ)
    (hB : ∀ᵐ ω ∂(P.restrict A), ∀ m, B m ω ≤ 0)
    (hE : ∀ᵐ ω ∂(P.restrict A),
      Tendsto (fun m => E m ω) atTop (nhds (0 : ℝ)))
    (hLedger : ∀ᵐ ω ∂(P.restrict A), ∀ m,
      0 ≤ (1 + y ω + (y ω) ^ 2) + b ω - 2 + 2 * t ω +
        B m ω + E m ω) :
    False := by
  haveI : (ae (P.restrict A)).NeBot := ae_neBot.mpr hApos
  have hAll : ∀ᵐ ω ∂(P.restrict A),
      (0 ≤ y ω ∧ y ω ≤ 1 / 5 ∧ b ω ≤ 1 / 100 ∧ t ω ≤ 1 / 10) ∧
      (∀ m, B m ω ≤ 0) ∧
      Tendsto (fun m => E m ω) atTop (nhds (0 : ℝ)) ∧
      (∀ m, 0 ≤ (1 + y ω + (y ω) ^ 2) + b ω - 2 + 2 * t ω +
        B m ω + E m ω) := by
    filter_upwards [hBounds, hB, hE, hLedger] with ω hbound hb he hl
    exact ⟨hbound, hb, he, hl⟩
  obtain ⟨ω, ⟨⟨h0, hcap, hb, ht⟩, hBω, hEω, hLω⟩⟩ := hAll.exists
  exact avram_jump6_A_physical_unitmark_ruin_gap_blocks_vanishing_signed_mesh
    (y ω) (b ω) (t ω) h0 hcap hb ht
    (fun m => B m ω) (fun m => E m ω) hBω hEω hLω
