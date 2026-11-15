-- Prove2me | solution 1 for AvramDividend.Classical.avram_b25_geometric_original_L1_integrable_mesh_increments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T01:03:32.919098+00:00
-- url     : https://prove2.me/submissions/94c742fc-3c5a-4c5a-909d-64c0aafcb198

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_simultaneous_geometric_L1_subsequence_from_original_three_cauchy_sources
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped NNReal ENNReal BigOperators
set_option pp.explicit true
set_option pp.fullNames true
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (G J E : ℕ → Ω → ℝ)
    (hGI : ∀ k, Integrable (G k) P)
    (hJI : ∀ k, Integrable (J k) P)
    (hEI : ∀ k, Integrable (E k) P)
    (hG : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m l : ℕ,
      N ≤ m → N ≤ l → (∫ ω, ‖G m ω - G l ω‖ ∂P) ≤ ε)
    (hJ : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m l : ℕ,
      N ≤ m → N ≤ l → (∫ ω, ‖J m ω - J l ω‖ ∂P) ≤ ε)
    (hE : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m : ℕ,
      N ≤ m → (∫ ω, ‖E m ω‖ ∂P) ≤ ε) :
    ∃ K : ℕ → ℕ,
      StrictMono K ∧
      (∀ k, Integrable (fun ω => G (K (k + 1)) ω - G (K k) ω) P) ∧
      (∀ k, Integrable (fun ω => J (K (k + 1)) ω - J (K k) ω) P) ∧
      (∀ k, Integrable (E (K k)) P) ∧
      (∀ k, (∫ ω, ‖G (K (k + 1)) ω - G (K k) ω‖ ∂P)
        ≤ ((1 : ℝ) / 2) ^ k) ∧
      (∀ k, (∫ ω, ‖J (K (k + 1)) ω - J (K k) ω‖ ∂P)
        ≤ ((1 : ℝ) / 2) ^ k) ∧
      (∀ k, (∫ ω, ‖E (K k) ω‖ ∂P)
        ≤ ((1 : ℝ) / 2) ^ k) := by
  obtain ⟨K, hStrict, hGgeom, hJgeom, hEgeom⟩ :=
    AvramDividend.Classical.avram_b24_simultaneous_geometric_L1_subsequence_from_original_three_cauchy_sources
      P G J E hG hJ hE
  refine ⟨K, hStrict, ?_, ?_, ?_, hGgeom, hJgeom, hEgeom⟩
  · intro k
    exact (hGI (K (k + 1))).sub (hGI (K k))
  · intro k
    exact (hJI (K (k + 1))).sub (hJI (K k))
  · intro k
    exact hEI (K k)
