-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB111_stopped_gaussian_L1_limit_inherits_eventual_mesh_tube
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:16:21.107958+00:00
-- url     : https://prove2.me/submissions/edd1af41-d467-4afa-86c7-113085ad0cf6

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB62_original_eventwise_L1_noise_limit_inherits_path_tube
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- Eventual mesh tube control passes to the stopped source L1 limit. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : Set Ω) (hA : MeasurableSet A)
    (N : Ω → ℝ) (M : ℕ → Ω → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (m0 : ℕ) (hNI : Integrable N (P.restrict A))
    (hMI : ∀ m, Integrable (M m) (P.restrict A))
    (hBound : ∀ m, m0 ≤ m → ∀ ω, ω ∈ A → |M m ω| ≤ ε)
    (hL1 : Tendsto (fun m => ∫ ω in A, |N ω - M m ω| ∂P)
      atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂(P.restrict A), |N ω| ≤ ε := by
  let M' : ℕ → Ω → ℝ := fun m => M (m + m0)
  have hMI' (m : ℕ) : Integrable (M' m) (P.restrict A) :=
    hMI (m + m0)
  have hBound' (m : ℕ) (ω : Ω) (hω : ω ∈ A) :
      |M' m ω| ≤ ε :=
    hBound (m + m0) (by omega) ω hω
  have hL1' : Tendsto
      (fun m => ∫ ω in A, |N ω - M' m ω| ∂P)
      atTop (𝓝 (0 : ℝ)) := by
    change Tendsto
      ((fun n : ℕ => ∫ ω in A, |N ω - M n ω| ∂P) ∘
        (fun m : ℕ => m + m0))
      atTop (𝓝 (0 : ℝ))
    exact hL1.comp (Filter.tendsto_add_atTop_nat m0)
  exact avram_gbB62_original_eventwise_L1_noise_limit_inherits_path_tube
    P A hA N M' ε hε hNI hMI' hBound' hL1'
