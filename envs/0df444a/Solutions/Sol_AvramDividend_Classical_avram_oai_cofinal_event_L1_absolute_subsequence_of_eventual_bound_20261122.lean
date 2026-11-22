-- Prove2me | solution 1 for AvramDividend.Classical.avram_oai_cofinal_event_L1_absolute_subsequence_of_eventual_bound_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T21:11:31.464672+00:00
-- url     : https://prove2.me/submissions/65b24ce5-e562-485d-82e7-bc6dd61bffc4

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_abs_L1_global_to_restricted
open MeasureTheory Set Filter Topology AvramDividend.Classical
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : ℕ → Ω → ℝ)
    (hSmall : ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
        Integrable (B m) P ∧
          (∫ ω, |B m ω| ∂P) ≤ ε) :
    ∃ r : ℕ → ℕ,
      (∀ j, Integrable (B (r j)) P) ∧
      (∀ A : Set Ω,
        (∀ j, Integrable (fun ω => |B (r j) ω|) (P.restrict A)) ∧
        Tendsto (fun j => ∫ ω in A, |B (r j) ω| ∂P)
          atTop (𝓝 (0 : ℝ)))  := by
  classical
  have hEvery : ∀ j : ℕ, ∃ m : ℕ,
      Integrable (B m) P ∧
        (∫ ω, |B m ω| ∂P) ≤ (1 : ℝ) / ((j : ℝ) + 1) := by
    intro j
    have hpos : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    obtain ⟨N, hN⟩ := hSmall _ hpos
    exact ⟨N, hN N (le_refl N)⟩
  let r : ℕ → ℕ := fun j => Classical.choose (hEvery j)
  have hInt : ∀ j, Integrable (B (r j)) P := by
    intro j
    exact (Classical.choose_spec (hEvery j)).1
  have hAbsInt : ∀ j,
      Integrable (fun ω => |B (r j) ω|) P := by
    intro j
    exact (hInt j).abs
  have hNonneg : ∀ j : ℕ,
      (0 : ℝ) ≤ ∫ ω, |B (r j) ω| ∂P := by
    intro j
    exact integral_nonneg (fun ω => abs_nonneg _)
  have hBound : ∀ j : ℕ,
      (∫ ω, |B (r j) ω| ∂P) ≤
        (1 : ℝ) / ((j : ℝ) + 1) := by
    intro j
    exact (Classical.choose_spec (hEvery j)).2
  have hInv : Tendsto
      (fun j : ℕ => (1 : ℝ) / ((j : ℝ) + 1))
        atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hAbsLim : Tendsto
      (fun j => ∫ ω, |B (r j) ω| ∂P)
        atTop (𝓝 (0 : ℝ)) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hInv hNonneg hBound
  refine ⟨r, hInt, ?_⟩
  intro A
  exact avram_ga_abs_L1_global_to_restricted P A
    (fun j => B (r j)) hAbsInt hAbsLim
