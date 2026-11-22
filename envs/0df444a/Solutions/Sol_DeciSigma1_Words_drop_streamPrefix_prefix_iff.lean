-- Prove2me | solution 1 for DeciSigma1.Words.drop_streamPrefix_prefix_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:13:10.937805+00:00
-- url     : https://prove2.me/submissions/7d5bfbab-0bcc-40dd-adce-d4ffdd5da4e3

module
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Theorems.Thm_DeciSigma1_Words_drop_streamPrefix
public import Theorems.Thm_DeciSigma1_Words_streamPrefix_prefix_iff

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Words (pow)
variable {α : Type}
namespace DeciSigma1.Words
theorem _root_.solution (ξ η : ℕ → α) {L L' a b : ℕ} (hb : b ≤ L) (ha : a ≤ L') :
    (streamPrefix η L).drop b <+: (streamPrefix ξ L').drop a ↔
      L - b ≤ L' - a ∧ ∀ t < L - b, η (b + t) = ξ (a + t) := by
  rw [drop_streamPrefix η hb, drop_streamPrefix ξ ha, streamPrefix_prefix_iff]
end DeciSigma1.Words
