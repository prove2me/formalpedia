-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward80m_nonpositive_right_dividend_and_continuous_gradient_loss_signed_upper_L1_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T16:32:44.687248+00:00
-- url     : https://prove2.me/submissions/5da51747-417e-4cd2-9533-31b7079b4ce2

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward80g_upper_L1_to_positive_gap
open MeasureTheory Set Filter Topology AvramDividend.Classical
noncomputable section

/-- Original nonpositive right-dividend and continuous gradient losses
may be discarded from a signed upper Ito source. Requiring the entire
residual to vanish in absolute L1 is unnecessary. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (G U V : Ω → ℝ) (Q : ℕ → Ω → ℝ)
    (ε : ℝ) (hε : 0 < ε)
    (hSource : ∃ (K : Ω → ℝ) (E : ℕ → Ω → ℝ),
      Integrable K P ∧ (∫ ω, |K ω| ∂P) ≤ ε / 4 ∧
      (∀ k, Integrable (E k) P) ∧
      (∀ k, ∀ᵐ ω ∂P,
        V ω - U ω ≤ K ω + Q k ω + E k ω) ∧
      Tendsto (fun k : ℕ => ∫ ω, |E k ω| ∂P)
        Filter.atTop (𝓝 (0 : ℝ)))
    (hQ : ∀ k, ∀ᵐ ω ∂P, Q k ω ≤ 0)
    (hGapI : Integrable (fun ω => G ω - U ω) P)
    (hCompare : ∀ᵐ ω ∂P,
      G ω - U ω ≤ max (0 : ℝ) (V ω - U ω)) :
    (∫ ω, max (0 : ℝ) (G ω - U ω) ∂P) ≤ ε / 2 := by
  obtain ⟨K, E, hKI, hKsmall, hEI, hUpper, hVan⟩ := hSource
  have hUpper' (k : ℕ) :
      ∀ᵐ ω ∂P, V ω - U ω ≤ K ω + E k ω := by
    filter_upwards [hUpper k, hQ k] with ω hA hB
    linarith
  exact avram_pj_reward80g_upper_L1_to_positive_gap
    P G U V ε hε
    ⟨K, E, hKI, hKsmall, hEI, hUpper', hVan⟩
    hGapI hCompare
