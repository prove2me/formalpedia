-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_spatial_true_Hk_R_Jfull_firstsize2_model_mesh_inconsistency
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T16:16:40.668929+00:00
-- url     : https://prove2.me/submissions/4dab468b-fa0e-4a94-a0b8-4e775e2bc124

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_ruin_truncated_spatial_clock_equals_first_size2_mark_all_k
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_spatial_Hsource_at_true_first_negative_size2_mark_equals_zero
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_spatial_fullmark_R_mesh_certificate_impossible_on_physical_first_ruin_event
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (A : Set Ω) (hA : P.restrict A ≠ 0)
    (B : ℝ≥0 → Ω → ℝ) (N : ℝ≥0 → Ω → ℕ)
    (σ ρ : Ω → ℝ≥0) (κ : ℕ → Ω → ℝ≥0)
    (q : ℝ) (w : ℝ → ℝ)
    (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwValue : w (1 / 10 : ℝ) = 1 + (1 / 10 : ℝ) + (1 / 10 : ℝ) ^ 2)
    (H : ℕ → Ω → ℝ) (R Jfull : ℝ≥0 → Ω → ℝ)
    (Drift Err : ℕ → Ω → ℝ) (k : ℕ)
    (hModel : ∀ᵐ ω ∂(P.restrict A),
      (∀ t : ℝ≥0, X.X t ω = B t ω - 2 * (N t ω : ℝ)) ∧
      (∀ t : ℝ≥0, t ≤ σ ω → |B t ω| < (1 / 4000 : ℝ)) ∧
      (∀ t : ℝ≥0, t < σ ω → N t ω = 0) ∧
      N (σ ω) ω = 1 ∧ 0 < σ ω ∧ (σ ω : ℝ) ≤ 1 / 500)
    (hρ : ∀ ω, ρ ω =
      (min (ruinTime X (1 / 10 : ℝ)
        (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω)
        (1 : ℝ≥0∞)).toNNReal)
    (hκ : ∀ j ω, κ j ω =
      (min (ρ ω : ℝ≥0∞)
        (twoSidedExitUpTime X ((j : ℝ) + 1) ω)).toNNReal)
    (hHsource : ∀ j ω, H j ω =
      Real.exp (-(q * (κ j ω : ℝ))) *
      w (if κ j ω = 0 ∨
            (κ j ω : ℝ≥0∞) <
              ruinTime X (1 / 10 : ℝ)
                (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω then
          (1 / 10 : ℝ) + X.X (κ j ω) ω -
            rightLimit
              (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ))
              (κ j ω) ω
         else
           riskProcess X (1 / 10 : ℝ)
             (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ))
             (κ j ω) ω) +
      (∫⁻ s in paymentTimes
          (ruinTime X (1 / 10 : ℝ)
            (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω)
          ∩ Iic (κ j ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure
           (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω)).toReal)
    (hNoise : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      R t ω = B t ω ∧ Jfull t ω = -2 * (N t ω : ℝ) + 2 * (t : ℝ))
    (hDrift : ∀ᵐ ω ∂(P.restrict A), ∀ m, Drift m ω ≤ 0)
    (hErr : ∀ᵐ ω ∂(P.restrict A),
      Tendsto (fun m => Err m ω) atTop (nhds (0 : ℝ)))
    (hLedger : ∀ᵐ ω ∂(P.restrict A), ∀ m,
      H k ω ≤ w (1 / 10 : ℝ) + R (κ k ω) ω +
        Jfull (κ k ω) ω + Drift m ω + Err m ω) :
    False := by
  have hK : ∀ᵐ ω ∂(P.restrict A), κ k ω = σ ω := by
    filter_upwards [hModel] with ω h
    rcases h with ⟨hp, ht, hb, hm, _, hs⟩
    exact (avram_jump6_A_actual_ruin_truncated_spatial_clock_equals_first_size2_mark_all_k
      X ω (fun t => B t ω) (fun t => N t ω)
      (σ ω) ρ κ hp ht hb (by omega : 1 ≤ N (σ ω) ω) hs
      (hρ ω) (fun j => hκ j ω)) k
  have hCash : ∀ᵐ ω ∂(P.restrict A), H k ω = 0 := by
    filter_upwards [hModel, hK] with ω h hk
    rcases h with ⟨hp, ht, hb, hm, hs, _⟩
    exact avram_jump6_A_original_spatial_Hsource_at_true_first_negative_size2_mark_equals_zero
      X ω (fun t => B t ω) (fun t => N t ω)
      (σ ω) hs hp ht hb (by omega : 1 ≤ N (σ ω) ω)
      q w hwneg H κ k hk hHsource
  have hTube : ∀ᵐ ω ∂(P.restrict A),
      B (σ ω) ω ≤ (1 / 100 : ℝ) := by
    filter_upwards [hModel] with ω h
    exact le_trans (le_of_lt (abs_lt.mp (h.2.1 (σ ω) le_rfl)).2)
      (by norm_num)
  have hMark : ∀ᵐ ω ∂(P.restrict A),
      (N (σ ω) ω : ℝ) = 1 := by
    filter_upwards [hModel] with ω h
    exact_mod_cast h.2.2.2.1
  have hClock : ∀ᵐ ω ∂(P.restrict A),
      (σ ω : ℝ) ≤ 1 / 10 := by
    filter_upwards [hModel] with ω h
    linarith [h.2.2.2.2.2]
  have hLed : ∀ᵐ ω ∂(P.restrict A), ∀ m,
      H k ω ≤ (1 + (1 / 10 : ℝ) + (1 / 10 : ℝ) ^ 2) +
        R (κ k ω) ω + Jfull (κ k ω) ω +
        Drift m ω + Err m ω := by
    filter_upwards [hLedger] with ω hl
    intro m
    simpa only [hwValue] using hl m
  exact avram_jump6_A_original_spatial_fullmark_R_mesh_certificate_impossible_on_physical_first_ruin_event
    P A hA B (fun t ω => (N t ω : ℝ)) R Jfull σ κ H Drift Err k
    hK hCash hNoise hTube hMark hClock hDrift hErr hLed
