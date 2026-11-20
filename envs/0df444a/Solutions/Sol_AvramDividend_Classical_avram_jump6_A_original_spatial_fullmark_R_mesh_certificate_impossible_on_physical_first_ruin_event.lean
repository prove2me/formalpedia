-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_spatial_fullmark_R_mesh_certificate_impossible_on_physical_first_ruin_event
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T16:11:48.689832+00:00
-- url     : https://prove2.me/submissions/131630d0-7a82-4806-a30f-3e0d39f68500

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_positive_event_stopped_cash_zero_excludes_fullmark_mesh_with_vanishing_error
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
    (B N R Jfull : ℝ≥0 → Ω → ℝ)
    (σ : Ω → ℝ≥0) (κ : ℕ → Ω → ℝ≥0)
    (H : ℕ → Ω → ℝ) (Drift Err : ℕ → Ω → ℝ)
    (k : ℕ)
    (hκ : ∀ᵐ ω ∂(P.restrict A), κ k ω = σ ω)
    (hCash : ∀ᵐ ω ∂(P.restrict A), H k ω = 0)
    (hNoise : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      R t ω = B t ω ∧
      Jfull t ω = -2 * N t ω + 2 * (t : ℝ))
    (hTube : ∀ᵐ ω ∂(P.restrict A),
      B (σ ω) ω ≤ (1 / 100 : ℝ))
    (hMark : ∀ᵐ ω ∂(P.restrict A), N (σ ω) ω = 1)
    (hClock : ∀ᵐ ω ∂(P.restrict A),
      (σ ω : ℝ) ≤ 1 / 10)
    (hDrift : ∀ᵐ ω ∂(P.restrict A), ∀ m, Drift m ω ≤ 0)
    (hErr : ∀ᵐ ω ∂(P.restrict A),
      Tendsto (fun m => Err m ω) atTop (nhds (0 : ℝ)))
    (hLedger : ∀ᵐ ω ∂(P.restrict A), ∀ m,
      H k ω ≤ (1 + (1 / 10 : ℝ) + (1 / 10 : ℝ) ^ 2) +
        R (κ k ω) ω + Jfull (κ k ω) ω +
        Drift m ω + Err m ω) :
    False := by
  have hOnA : ∀ᵐ ω ∂(P.restrict A), ∀ t : ℝ≥0,
      R t ω = B t ω ∧ Jfull t ω = -2 * N t ω + 2 * (t : ℝ) :=
    ae_restrict_of_ae hNoise
  have hFull : ∀ᵐ ω ∂(P.restrict A),
      Jfull (κ k ω) ω =
        -2 * N (σ ω) ω + 2 * (σ ω : ℝ) := by
    filter_upwards [hOnA, hκ] with ω hn hk
    rw [hk]
    exact (hn (σ ω)).2
  have hLed : ∀ᵐ ω ∂(P.restrict A), ∀ m,
      H k ω ≤ (1 + (1 / 10 : ℝ) + (1 / 10 : ℝ) ^ 2) +
        B (σ ω) ω + Jfull (κ k ω) ω +
        Drift m ω + Err m ω := by
    filter_upwards [hOnA, hκ, hLedger] with ω hn hk hl
    intro m
    have hR : R (κ k ω) ω = B (σ ω) ω := by
      rw [hk]
      exact (hn (σ ω)).1
    simpa only [hR] using hl m
  exact avram_jump6_A_original_positive_event_stopped_cash_zero_excludes_fullmark_mesh_with_vanishing_error
    P A hA B N σ (fun ω => H k ω) (fun ω => Jfull (κ k ω) ω)
    Drift Err hTube hMark hClock hCash hFull hDrift hErr hLed
