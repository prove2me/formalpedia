-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_positive_ruin_mark_event_refutes_original_unit_fullmark_cash_certificate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T09:34:30.454226+00:00
-- url     : https://prove2.me/submissions/fbc27634-595d-43eb-9447-1bc3f02e67cc

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Set Ω) (hA : P.restrict A ≠ 0)
    (H R Jfull t : Ω → ℝ) (N : Ω → ℕ)
    (hPhysical : ∀ᵐ ω ∂(P.restrict A),
      H ω = 0 ∧ R ω ≤ 1 / 4000 ∧ t ω ≤ 1 / 500 ∧
      1 ≤ N ω ∧ Jfull ω = -2 * (N ω : ℝ) + 2 * t ω)
    (hCertificate : ∃ B : Ω → ℝ,
      (∀ᵐ ω ∂(P.restrict A), B ω ≤ 0) ∧
      (∀ᵐ ω ∂(P.restrict A),
        H ω ≤ (111 / 100 : ℝ) + R ω + Jfull ω + B ω)) :
    False := by
  letI : (ae (P.restrict A)).NeBot := ae_neBot.mpr hA
  obtain ⟨B, hB, hLedger⟩ := hCertificate
  have hAll : ∀ᵐ ω ∂(P.restrict A),
      (H ω = 0 ∧ R ω ≤ 1 / 4000 ∧ t ω ≤ 1 / 500 ∧
        1 ≤ N ω ∧ Jfull ω = -2 * (N ω : ℝ) + 2 * t ω) ∧
      B ω ≤ 0 ∧
      H ω ≤ (111 / 100 : ℝ) + R ω + Jfull ω + B ω := by
    filter_upwards [hPhysical, hB, hLedger] with ω hphys hb hcash
    exact ⟨hphys, hb, hcash⟩
  obtain ⟨ω, ⟨⟨hH, hR, ht, hN, hJ⟩, hb, hc⟩⟩ := hAll.exists
  have hNat : (1 : ℝ) ≤ (N ω : ℝ) := by exact_mod_cast hN
  rw [hH, hJ] at hc
  linarith
