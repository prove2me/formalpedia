-- Prove2me | solution 1 for Formalism.CountingSumsFrames.window_parameter_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:01:59.465101+00:00
-- url     : https://prove2.me/submissions/750ab3aa-11bc-4190-b144-ee47afe9f8d0

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentTopRoomPublished

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution {p N N₁ r : ℕ} {Y a b' Q La : ℝ} (h : HypSeg p N N₁ (r + 1) Y a b' Q La) :
    1 ≤ Y ∧ ((r : ℝ) + 1) ^ 2 * Y ^ 2 ≤ p ∧ ((r : ℝ) + 1) * Y ^ 2 * Real.log a ≤ a / b' ∧
    (N : ℝ) ≤ (r : ℝ) + 1 ∧ (N₁ : ℝ) ^ 4 ≤ (r : ℝ) + 1 ∧ Real.log a ≤ (r : ℝ) + 1 ∧ 0 ≤ La ∧
    La ≤ (r : ℝ) + 1 ∧ ((r : ℝ) + 1) ^ 3 * Q * Y ≤ b' ∧ b' ≤ a ∧ (p : ℝ) < a / b' ∧
    (3 : ℝ) ≤ (r : ℝ) + 1 ∧ (1 : ℝ) ≤ N ∧ (1 : ℝ) ≤ N₁ ∧ 1 ≤ Q ∧ 0 < b' := by
  obtain ⟨hY, hp, h2, hN, hN1, hlog, hLa0, hLa, h4, hba, h6, hk, hN', hN1', hQ, hb0⟩ := h
  push_cast at hp h2 hlog hLa h4
  exact ⟨hY, hp, h2, by exact_mod_cast hN, by exact_mod_cast hN1, hlog, hLa0, hLa, h4, hba, h6,
    by exact_mod_cast hk, by exact_mod_cast hN', by exact_mod_cast hN1', hQ, hb0⟩
end Formalism.CountingSumsFrames
