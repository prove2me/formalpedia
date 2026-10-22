-- Prove2me | solution 1 for GDPRDataMarkets.Benchmark.personalized_price
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:18:04.955097+00:00
-- url     : https://prove2.me/submissions/48ccf5c4-e73b-4e13-a318-12071656224f

import Mathlib
import Definitions.Def_GDPRDataMarkets_Benchmark_Model
set_option autoImplicit false
open MeasureTheory
open GDPRDataMarkets.Benchmark

theorem solution (P : Params) (hS : P.Standing) (hμ : 3 * P.sigma - 1 ≤ P.mu)
    (v : ℝ) (hv : 0 ≤ v) :
    (∀ ρ : ℝ, RB P v ρ ≤ RB P v ((1 + P.mu - P.sigma) * v)) ∧
    (1 + P.mu - P.sigma) * v = (1 + P.kL) * v ∧
    (1 + P.mu - P.sigma) * v ≤ (1 + P.kL) * v ∧
    (1 + P.mu - P.sigma) * v ≤ (1 + P.kH) * v := by
  obtain ⟨hL, hLH, _, _, _⟩ := hS
  have hmu : P.mu - P.sigma = P.kL := by unfold Params.mu Params.sigma; ring
  have hkey : (1 + P.mu - P.sigma) = 1 + P.kL := by linarith
  have hμ' : P.kH ≤ 1 + 2 * P.kL := by unfold Params.mu Params.sigma at hμ; linarith
  rw [hkey]
  refine ⟨?_, rfl, le_refl _, ?_⟩
  · intro ρ
    have hstar : RB P v ((1 + P.kL) * v) = (1 + P.kL) * v := by
      unfold RB revB
      rw [if_pos (le_refl _), if_pos (by nlinarith)]
      ring
    rw [hstar]
    unfold RB revB
    have hvL : 0 ≤ (1 + P.kL) * v := by positivity
    by_cases h1 : ρ ≤ (1 + P.kL) * v
    · rw [if_pos h1, if_pos (by nlinarith)]; linarith
    · rw [if_neg h1]
      by_cases h2 : ρ ≤ (1 + P.kH) * v
      · rw [if_pos h2]; nlinarith
      · rw [if_neg h2]; linarith
  · nlinarith
