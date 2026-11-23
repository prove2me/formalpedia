-- Prove2me | solution 1 for ChenCapacityTerminals.Exact.guide_entries
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:40:54.823975+00:00
-- url     : https://prove2.me/submissions/00bc7271-9ff8-4dda-8999-000d2b881813

import Theorems.Thm_ChenCapacityTerminals_Exact_whole_target_charges
import Theorems.Thm_ChenCapacityTerminals_Exact_mixed_target_round_charges
import Theorems.Thm_ChenCapacityTerminals_Exact_mixed_target_rank_charges
import Definitions.Def_ChenCapacityTerminals_Exact_GuideTargets

set_option autoImplicit false

open ChenCapacityTerminals.Exact

theorem solution (G : Network) (r d : ℕ) (L : ℚ) (b : ℕ → ℕ) (t : ℕ)
    (c : Construction) (X : Finset ℕ)
    (hG : Prepared G r) (hd : 1 ≤ d) (hdn : d ≤ G.vertices.card)
    (hL : 0 < L) (hlower : RootLowerBound G r L)
    (hc : LegalConstruction G r d L b t c)
    (hX : X ⊆ G.vertices \ (c.earlyProbes G r ((L : ℝ) / (4 * d)) ∪ {r})) :
    (guideEntries (c.guide G ((L : ℝ) / (4 * d))) X : ℝ) ≤
      (1 + (min c.rounds (Nat.log2 G.vertices.card) : ℕ)) * cut G X /
        ((L : ℝ) / (4 * d)) := by
  let τ : ℝ := (L : ℝ) / (4 * d)
  have hwhole : (wholeTargetEntries c G τ X : ℝ) ≤ cut G X / τ := by
    exact whole_target_charges G r d L b t c X hG hd hdn hL hlower hc hX
  have hround : (mixedTargetEntries c G τ X : ℝ) ≤ c.rounds * cut G X / τ := by
    exact mixed_target_round_charges G r d L b t c X hG hd hdn hL hlower hc hX
  have hrank :
      (mixedTargetEntries c G τ X : ℝ) ≤
        (Nat.log2 G.vertices.card) * cut G X / τ := by
    exact mixed_target_rank_charges G r d L b t c X hG hd hdn hL hlower hc hX
  have hmixed :
      (mixedTargetEntries c G τ X : ℝ) ≤
        (min c.rounds (Nat.log2 G.vertices.card) : ℕ) * cut G X / τ := by
    rcases le_total c.rounds (Nat.log2 G.vertices.card) with h | h
    · rw [min_eq_left h]
      exact hround
    · rw [min_eq_right h]
      exact hrank
  have hsplit :
      (guideEntries (c.guide G τ) X : ℝ) =
        (wholeTargetEntries c G τ X : ℝ) + (mixedTargetEntries c G τ X : ℝ) := by
    exact_mod_cast guideEntries_eq_wholeTargetEntries_add_mixedTargetEntries c G τ X
  change (guideEntries (c.guide G τ) X : ℝ) ≤ _
  rw [hsplit]
  calc
    (wholeTargetEntries c G τ X : ℝ) + (mixedTargetEntries c G τ X : ℝ)
        ≤ cut G X / τ + (min c.rounds (Nat.log2 G.vertices.card) : ℕ) * cut G X / τ :=
      add_le_add hwhole hmixed
    _ = (1 + (min c.rounds (Nat.log2 G.vertices.card) : ℕ)) * cut G X / τ := by
      push_cast
      ring
