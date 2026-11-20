-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_positive_event_stopped_cash_zero_excludes_fullmark_mesh_with_vanishing_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T15:38:50.599101+00:00
-- url     : https://prove2.me/submissions/795545a2-5b26-4b03-9b2c-377eaff0bbb1

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_positive_measure_ruin_gap_excludes_physical_mesh
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Set Ω) (hA : P.restrict A ≠ 0)
    (B N : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0)
    (H Jfull : Ω → ℝ) (Drift Err : ℕ → Ω → ℝ)
    (hTube : ∀ᵐ ω ∂(P.restrict A),
      B (σ ω) ω ≤ (1 / 100 : ℝ))
    (hMark : ∀ᵐ ω ∂(P.restrict A), N (σ ω) ω = 1)
    (hClock : ∀ᵐ ω ∂(P.restrict A), (σ ω : ℝ) ≤ 1 / 10)
    (hCash : ∀ᵐ ω ∂(P.restrict A), H ω = 0)
    (hFull : ∀ᵐ ω ∂(P.restrict A),
      Jfull ω = -2 * N (σ ω) ω + 2 * (σ ω : ℝ))
    (hDrift : ∀ᵐ ω ∂(P.restrict A), ∀ m, Drift m ω ≤ 0)
    (hErr : ∀ᵐ ω ∂(P.restrict A),
      Tendsto (fun m => Err m ω) atTop (nhds (0 : ℝ)))
    (hLedger : ∀ᵐ ω ∂(P.restrict A), ∀ m,
      H ω ≤ (1 + (1 / 10 : ℝ) + (1 / 10 : ℝ) ^ 2) +
        B (σ ω) ω + Jfull ω + Drift m ω + Err m ω) :
    False := by
  have hBounds : ∀ᵐ ω ∂(P.restrict A),
      0 ≤ (1 / 10 : ℝ) ∧ (1 / 10 : ℝ) ≤ 1 / 5 ∧
      B (σ ω) ω ≤ 1 / 100 ∧ (σ ω : ℝ) ≤ 1 / 10 := by
    filter_upwards [hTube, hClock] with ω hb ht
    exact ⟨by norm_num, by norm_num, hb, ht⟩
  have hRaw : ∀ᵐ ω ∂(P.restrict A), ∀ m,
      0 ≤ (1 + (1 / 10 : ℝ) + (1 / 10 : ℝ) ^ 2) +
        B (σ ω) ω - 2 + 2 * (σ ω : ℝ) +
        Drift m ω + Err m ω := by
    filter_upwards [hMark, hCash, hFull, hLedger] with ω hn hCash' hFull' hLedger'
    intro m
    have hm := hLedger' m
    rw [hCash', hFull', hn] at hm
    nlinarith
  exact avram_jump6_A_positive_measure_ruin_gap_excludes_physical_mesh
    P A hA (fun _ => (1 / 10 : ℝ)) (fun ω => B (σ ω) ω)
    (fun ω => (σ ω : ℝ)) hBounds Drift Err hDrift hErr hRaw
