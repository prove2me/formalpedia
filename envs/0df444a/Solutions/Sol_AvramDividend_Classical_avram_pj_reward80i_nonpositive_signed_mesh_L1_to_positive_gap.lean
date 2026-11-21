-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward80i_nonpositive_signed_mesh_L1_to_positive_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:46:56.153376+00:00
-- url     : https://prove2.me/submissions/536cc92f-a4fc-47dc-b8b2-b10b13875aa1

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward80g_upper_L1_to_positive_gap
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Nonpositive physical-grid right-payment corrections can be discarded
from a signed L1 residual without changing the original stopped payoff. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (G U V : Ω → ℝ) (Q : ℕ → Ω → ℝ)
    (ε : ℝ) (hε : 0 < ε)
    (hSource : ∃ (K : Ω → ℝ),
      Integrable K P ∧ (∫ ω, |K ω| ∂P) ≤ ε / 4 ∧
      (∀ k, Integrable (fun ω => V ω - U ω - K ω - Q k ω) P) ∧
      Tendsto (fun k : ℕ =>
        ∫ ω, |V ω - U ω - K ω - Q k ω| ∂P)
        Filter.atTop (𝓝 (0 : ℝ)))
    (hQ : ∀ k, ∀ᵐ ω ∂P, Q k ω ≤ 0)
    (hGapI : Integrable (fun ω => G ω - U ω) P)
    (hCompare : ∀ᵐ ω ∂P,
      G ω - U ω ≤ max (0 : ℝ) (V ω - U ω)) :
    (∫ ω, max (0 : ℝ) (G ω - U ω) ∂P) ≤ ε / 2 := by
  obtain ⟨K, hKI, hKsmall, hEI, hVan⟩ := hSource
  have hUpper : ∀ k : ℕ, ∀ᵐ ω ∂P,
      V ω - U ω ≤ K ω + (V ω - U ω - K ω - Q k ω) := by
    intro k
    filter_upwards [hQ k] with ω hQω
    linarith
  exact avram_pj_reward80g_upper_L1_to_positive_gap
    P G U V ε hε
    ⟨K, (fun k ω => V ω - U ω - K ω - Q k ω),
      hKI, hKsmall, hEI, hUpper, hVan⟩
    hGapI hCompare
