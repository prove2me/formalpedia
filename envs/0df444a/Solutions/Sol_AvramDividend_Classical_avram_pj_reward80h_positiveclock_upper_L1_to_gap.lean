-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward80h_positiveclock_upper_L1_to_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:50:38.794188+00:00
-- url     : https://prove2.me/submissions/56f358d7-ef98-498b-b073-a9d63502020f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward80g_upper_L1_to_positive_gap
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Transfer a positive-clock signed upper source through a zero-clock exact
cancellation, retaining all non-Gaussian, full-mark physical errors. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ρ : Ω → ℝ≥0) (G U V : Ω → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hSource : ∃ (K : Ω → ℝ) (E : ℕ → Ω → ℝ),
      Integrable K P ∧ (∫ ω, |K ω| ∂P) ≤ ε / 4 ∧
      (∀ k, Integrable (E k) P) ∧
      (∀ k, ∀ᵐ ω ∂P, 0 < ρ ω → V ω - U ω ≤ K ω + E k ω) ∧
      Tendsto (fun k : ℕ => ∫ ω, |E k ω| ∂P)
        Filter.atTop (𝓝 (0 : ℝ)))
    (hZero : ∀ᵐ ω ∂P, ρ ω = 0 → G ω = U ω)
    (hGapI : Integrable (fun ω => G ω - U ω) P)
    (hCompare : ∀ᵐ ω ∂P, 0 < ρ ω →
      G ω - U ω ≤ max (0 : ℝ) (V ω - U ω)) :
    (∫ ω, max (0 : ℝ) (G ω - U ω) ∂P) ≤ ε / 2 := by
  obtain ⟨K, E, hKI, hKsmall, hEI, hUpper, hVan⟩ := hSource
  let V' : Ω → ℝ := fun ω => if 0 < ρ ω then V ω else U ω
  have hUpper' : ∀ k : ℕ, ∀ᵐ ω ∂P,
      V' ω - U ω ≤ |K ω| + |E k ω| := by
    intro k
    filter_upwards [hUpper k] with ω hw
    by_cases hρ : 0 < ρ ω
    · dsimp [V']
      rw [if_pos hρ]
      exact (hw hρ).trans (add_le_add (le_abs_self _) (le_abs_self _))
    · dsimp [V']
      rw [if_neg hρ]
      simpa using add_nonneg (abs_nonneg (K ω)) (abs_nonneg (E k ω))
  have hSource' : ∃ (K' : Ω → ℝ) (E' : ℕ → Ω → ℝ),
      Integrable K' P ∧ (∫ ω, |K' ω| ∂P) ≤ ε / 4 ∧
      (∀ k, Integrable (E' k) P) ∧
      (∀ k, ∀ᵐ ω ∂P, V' ω - U ω ≤ K' ω + E' k ω) ∧
      Tendsto (fun k : ℕ => ∫ ω, |E' k ω| ∂P)
        Filter.atTop (𝓝 (0 : ℝ)) := by
    refine ⟨(fun ω => |K ω|), (fun k ω => |E k ω|),
      hKI.abs, ?_, (fun k => (hEI k).abs), hUpper', ?_⟩
    · simpa only [abs_abs] using hKsmall
    · simpa only [abs_abs] using hVan
  have hCompare' : ∀ᵐ ω ∂P,
      G ω - U ω ≤ max (0 : ℝ) (V' ω - U ω) := by
    filter_upwards [hCompare, hZero] with ω hc hz
    by_cases hρ : 0 < ρ ω
    · simpa only [V', if_pos hρ] using hc hρ
    · have hzρ : ρ ω = 0 :=
        le_antisymm (le_of_not_gt hρ) zero_le
      simp [V', hρ, hz hzρ]
  exact avram_pj_reward80g_upper_L1_to_positive_gap
    P G U V' ε hε hSource' hGapI hCompare'
