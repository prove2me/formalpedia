-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_positiveclock_mask_L2_to_global
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:32:39.35008+00:00
-- url     : https://prove2.me/submissions/bb9edf73-6618-454e-b223-0079954e373d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_signed_spatial_K_mask_preserves_L1
open scoped NNReal ENNReal
open MeasureTheory Set Filter Topology AvramDividend.Classical
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (ρ : Ω → ℝ≥0) (hS : MeasurableSet {ω : Ω | ρ ω ≠ 0})
    (V U : Ω → ℝ) (Q : ℕ → Ω → ℝ)
    (hVU : ∀ ω, ρ ω = 0 → V ω = U ω)
    (hQ0 : ∀ k ω, ρ ω = 0 → Q k ω = 0)
    (ε : ℝ) (K : Ω → ℝ)
    (hKI : Integrable K P)
    (hKsmall : (∫ ω, |K ω| ∂P) ≤ ε / 4)
    (hEI : ∀ k, Integrable
      (fun ω => if ρ ω = 0 then 0 else V ω - U ω - K ω - Q k ω) P)
    (E : ℕ → Ω → ℝ)
    (hEdef : ∀ k ω, E k ω =
      if ρ ω = 0 then 0 else V ω - U ω - K ω - Q k ω)
    (M : ℝ) (hM : 0 ≤ M)
    (hL2 : ∀ k, Integrable (fun ω => (|E k ω|)^2) P ∧
      (∫ ω, (|E k ω|)^2 ∂P) ≤ M)
    (hAE : ∀ᵐ ω ∂P, Tendsto (fun k : ℕ => E k ω)
      Filter.atTop (𝓝 (0 : ℝ))) :
    ∃ (K' : Ω → ℝ), Integrable K' P ∧
      (∫ ω, |K' ω| ∂P) ≤ ε / 4 ∧
      (∀ k, Integrable (fun ω => V ω - U ω - K' ω - Q k ω) P) ∧
      ∃ (E' : ℕ → Ω → ℝ),
        (∀ k ω, E' k ω = V ω - U ω - K' ω - Q k ω) ∧
        ∃ (M' : ℝ), 0 ≤ M' ∧
          (∀ k, Integrable (fun ω => (|E' k ω|)^2) P ∧
            (∫ ω, (|E' k ω|)^2 ∂P) ≤ M') ∧
          (∀ᵐ ω ∂P, Tendsto (fun k : ℕ => E' k ω)
            Filter.atTop (𝓝 (0 : ℝ))) := by 
  obtain ⟨K', hK'I, hK'small, hOff, hOn⟩ :=
    avram_pj_workerC_signed_spatial_K_mask_preserves_L1
      {ω : Ω | ρ ω ≠ 0} hS K hKI (ε / 4) hKsmall
  have hEq (k : ℕ) (ω : Ω) :
      V ω - U ω - K' ω - Q k ω = E k ω := by
    by_cases hz : ρ ω = 0
    · rw [hVU ω hz, hQ0 k ω hz, hOff ω (by simpa using hz)]
      simp [hEdef k ω, hz]
    · rw [hOn ω (by simpa using hz), hEdef k ω]
      simp [hz]
  refine ⟨K', hK'I, hK'small, ?_, E, ?_, M, hM, hL2, hAE⟩
  · intro k
    have hFun : (fun ω => V ω - U ω - K' ω - Q k ω) =
        (fun ω => if ρ ω = 0 then 0 else V ω - U ω - K ω - Q k ω) := by
      funext ω
      exact (hEq k ω).trans (hEdef k ω)
    rw [hFun]
    exact hEI k
  · intro k ω
    exact (hEq k ω).symm
