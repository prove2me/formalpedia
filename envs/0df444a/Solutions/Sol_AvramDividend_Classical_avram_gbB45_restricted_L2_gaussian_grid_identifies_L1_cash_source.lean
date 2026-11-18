-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB45_restricted_L2_gaussian_grid_identifies_L1_cash_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:05:55.956163+00:00
-- url     : https://prove2.me/submissions/eb96f51f-ff28-4723-ae1b-77a201e2f439

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_restricted_real_L1_two_limits_unique_ae
import Theorems.Thm_AvramDividend_Classical_avram_gb29_probabilistic_L2_to_eventwise_L1_transfer
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- Restricted L1 and full L2 Gaussian source limits coincide on the event. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : Set Ω)
    (M : ℕ → Ω → ℝ) (N J : Ω → ℝ)
    (hNI : Integrable N (P.restrict A))
    (hJI : Integrable J (P.restrict A))
    (hMI : ∀ m, Integrable (M m) (P.restrict A))
    (hL1 : Tendsto (fun m => ∫ ω in A, |N ω - M m ω| ∂P)
      atTop (𝓝 (0 : ℝ)))
    (hMLp : ∀ m, MemLp (M m) 2 P) (hJLp : MemLp J 2 P)
    (hL2 : Tendsto (fun m : ℕ => eLpNorm (M m - J) 2 P)
      atTop (𝓝 (0 : ℝ≥0∞))) :
    ∀ᵐ ω ∂(P.restrict A), N ω = J ω := by
  have hJ1 :=
    avram_gb29_probabilistic_L2_to_eventwise_L1_transfer
      P A M J hMLp hJLp hL2
  exact avram_ga_restricted_real_L1_two_limits_unique_ae
    P A N J M hNI hJI hMI hL1 hJ1
