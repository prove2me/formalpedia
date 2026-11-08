-- Prove2me | solution 1 for CondBasedProd.bracket_maximizers_monotone
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:53:43.227453+00:00
-- url     : https://prove2.me/submissions/7b258db9-0f7b-4901-a2ea-afe6b3a4d279

import Mathlib
import Definitions.Def_CondBasedProd_IsOptRate

open CondBasedProd in
theorem solution (M : Model) (y y' s s' : ℝ) (hy : y ≤ y') (hs : IsBracketMax M y s) (hs' : IsBracketMax M y' s') : IsBracketMax M y' (min s s') ∧ IsBracketMax M y (max s s') := by
  rcases le_total s s' with h | h
  · rw [min_eq_left h, max_eq_right h]
    have hf : M.f s ≤ M.f s' := M.f_mono hs.1 hs'.1 h
    have a := hs.2 s' hs'.1
    have b := hs'.2 s hs.1
    have c : 0 ≤ (M.f s' - M.f s) * (y' - y) := mul_nonneg (by linarith) (by linarith)
    refine ⟨⟨hs.1, fun t ht => ?_⟩, ⟨hs'.1, fun t ht => ?_⟩⟩
    · have := hs'.2 t ht; nlinarith
    · have := hs.2 t ht; nlinarith
  · rw [min_eq_right h, max_eq_left h]
    exact ⟨hs', hs⟩
