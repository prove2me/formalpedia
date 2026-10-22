-- Prove2me | solution 1 for CycleLengthsExp.WellSpread.ball_growth
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:46:56.976994+00:00
-- url     : https://prove2.me/submissions/c75d298f-e37b-4bb0-b245-acf0322e80c0

import Mathlib
import Definitions.Def_CycleLengthsExp_WellSpread_Setting

set_option autoImplicit false
open CycleLengthsExp.WellSpread

theorem clw_ball_growth {V : Type*} [Fintype V] (G : SimpleGraph V) (k α : ℝ)
    (hk : 0 < k) (hα : 0 < α) (hG : IsKAlphaExpander k α G) (v : V) (r : ℕ) :
    min k ((1 + α) ^ r) ≤ ((ball G v r).ncard : ℝ) := by
  induction r with
  | zero =>
    have h1 : 1 ≤ (ball G v 0).ncard := by
      apply Nat.succ_le_of_lt
      rw [Set.ncard_pos (Set.toFinite _)]
      exact ⟨v, SimpleGraph.Walk.nil, by simp⟩
    have h2 : (1 : ℝ) ≤ ((ball G v 0).ncard : ℝ) := by exact_mod_cast h1
    calc min k ((1 + α) ^ 0) ≤ (1 + α) ^ 0 := min_le_right _ _
      _ = 1 := pow_zero _
      _ ≤ _ := h2
  | succ r ih =>
    set B := ball G v r with hB
    have hsub : B ⊆ ball G v (r + 1) := by
      rintro w ⟨p, hp⟩
      exact ⟨p, by omega⟩
    have hext : extNbhd G B ⊆ ball G v (r + 1) := by
      rintro w ⟨hwB, u, ⟨p, hp⟩, hadj⟩
      refine ⟨p.concat hadj, ?_⟩
      rw [SimpleGraph.Walk.length_concat]; omega
    have hdisj : Disjoint B (extNbhd G B) := by
      rw [Set.disjoint_left]
      intro w hw hw'
      exact hw'.1 hw
    have hcard : B.ncard + (extNbhd G B).ncard ≤ (ball G v (r + 1)).ncard := by
      rw [← Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
      exact Set.ncard_le_ncard (Set.union_subset hsub hext) (Set.toFinite _)
    have hmono : B.ncard ≤ (ball G v (r + 1)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    have hmono' : (B.ncard : ℝ) ≤ ((ball G v (r + 1)).ncard : ℝ) := by exact_mod_cast hmono
    have hcard' : (B.ncard : ℝ) + ((extNbhd G B).ncard : ℝ) ≤ ((ball G v (r + 1)).ncard : ℝ) := by
      exact_mod_cast hcard
    by_cases hBk : (B.ncard : ℝ) ≤ k
    · have hexp := hG B hBk
      by_cases hr : (1 + α) ^ r ≤ (B.ncard : ℝ)
      · calc min k ((1 + α) ^ (r + 1)) ≤ (1 + α) ^ (r + 1) := min_le_right _ _
          _ = (1 + α) * (1 + α) ^ r := by ring
          _ ≤ (1 + α) * (B.ncard : ℝ) := by
              apply mul_le_mul_of_nonneg_left hr (by linarith)
          _ = (B.ncard : ℝ) + α * B.ncard := by ring
          _ ≤ _ := by linarith
      · push Not at hr
        have hkB : k ≤ (B.ncard : ℝ) := by
          by_contra hlt
          push Not at hlt
          have := lt_min hlt hr
          linarith
        calc min k ((1 + α) ^ (r + 1)) ≤ k := min_le_left _ _
          _ ≤ _ := hkB.trans hmono'
    · push Not at hBk
      calc min k ((1 + α) ^ (r + 1)) ≤ k := min_le_left _ _
        _ ≤ _ := hBk.le.trans hmono'

theorem solution {V : Type*} [Fintype V] (G : SimpleGraph V) (k α : ℝ)
    (hk : 0 < k) (hα : 0 < α) (hG : IsKAlphaExpander k α G) (v : V) (r : ℕ) :
    min k ((1 + α) ^ r) ≤ ((ball G v r).ncard : ℝ) := clw_ball_growth G k α hk hα hG v r
