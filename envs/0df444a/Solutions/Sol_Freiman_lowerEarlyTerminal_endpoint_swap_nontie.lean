-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_endpoint_swap_nontie
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T20:58:22.765238+00:00
-- url     : https://prove2.me/submissions/32bb384b-230a-487b-b621-5e6cbf85c7fe

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000

open Freiman

/-- Swapping a pair with distinct widths swaps the two words that
`lowerEqualWords` produces: the normalisation picks the same ordered pair, and only
the final re-orientation differs. -/
private theorem eqw_swap (u : LowerPair) (hu : lowerWidth u.1 ≠ lowerWidth u.2) (upper : Bool) :
    lowerEqualWords (u.2,u.1) upper
      = ((lowerEqualWords u upper).2, (lowerEqualWords u upper).1) := by
  have hn : lowerNormalize (u.2,u.1) = lowerNormalize u := by
    unfold lowerNormalize
    by_cases h : lowerWidth u.2 ≤ lowerWidth u.1
    · have h' : ¬ lowerWidth u.1 ≤ lowerWidth u.2 := fun hc => hu (le_antisymm hc h)
      simp [h, h']
    · have h' : lowerWidth u.1 ≤ lowerWidth u.2 := (not_le.mp h).le
      simp [h, h']
  unfold lowerEqualWords
  rw [hn]
  by_cases h : lowerWidth u.2 ≤ lowerWidth u.1
  · have h' : ¬ lowerWidth u.1 ≤ lowerWidth u.2 := fun hc => hu (le_antisymm hc h)
    simp [h, h']
  · have h' : lowerWidth u.1 ≤ lowerWidth u.2 := (not_le.mp h).le
    simp [h, h']

/-- `lowerNaturalWords` acts componentwise, so it is swap-equivariant outright. -/
private theorem nat_swap (w : LowerPair) (upper : Bool) :
    lowerNaturalWords (w.2,w.1) upper
      = ((lowerNaturalWords w upper).2, (lowerNaturalWords w upper).1) := rfl

/-- Swap-equivariance of the endpoint word selection. -/
private theorem words_swap (w : LowerPair) (hn : LowerEarlyTerminalNoTies w) (upper : Bool) :
    lowerEndpointWords (w.2,w.1) upper
      = ((lowerEndpointWords w upper).2, (lowerEndpointWords w upper).1) := by
  obtain ⟨hne, hmix⟩ := hn
  unfold lowerEndpointWords
  by_cases hpar : w.1.length % 2 = w.2.length % 2
  · rw [if_pos hpar.symm, if_pos hpar]
    exact eqw_swap w hne upper
  · obtain ⟨hm1, hm2⟩ := hmix hpar
    have hpar' : ¬ (w.2.length % 2 = w.1.length % 2) := fun hc => hpar hc.symm
    rw [if_neg hpar', if_neg hpar]
    by_cases h : lowerWidth w.2 ≤ lowerWidth w.1
    · have h' : ¬ lowerWidth w.1 ≤ lowerWidth w.2 := fun hc => hne (le_antisymm hc h)
      simp only [h, h', if_true, if_false]
      by_cases hu : upper = decide (w.1.length % 2 = 0)
      · simp only [if_pos hu]
        exact eqw_swap (w.1 ++ [1], w.2) hm1 upper
      · simp only [if_neg hu]
        exact nat_swap w upper
    · have h' : lowerWidth w.1 ≤ lowerWidth w.2 := (not_le.mp h).le
      simp only [h, h', if_true, if_false]
      by_cases hu : upper = decide (w.2.length % 2 = 0)
      · simp only [if_pos hu]
        exact eqw_swap (w.1, w.2 ++ [1]) hm2 upper
      · simp only [if_neg hu]
        exact nat_swap w upper

theorem solution (w : LowerPair) (hn : LowerEarlyTerminalNoTies w) (upper : Bool) :
    lowerEndpoint w upper = lowerEndpoint (w.2,w.1) upper := by
  unfold lowerEndpoint
  rw [words_swap w hn upper]
  ring
