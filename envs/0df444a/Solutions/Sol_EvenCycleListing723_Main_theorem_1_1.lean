-- Prove2me | solution 1 for EvenCycleListing723.Main.theorem_1_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T05:42:25.779903+00:00
-- url     : https://prove2.me/submissions/01379c74-4790-44ef-ae35-eb149a83ce69
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_EvenCycleListing723_Main_exploration_bound
import Theorems.Thm_EvenCycleListing723_Main_ram_listing

set_option autoImplicit false
open EvenCycleListing723.Main

theorem solution (k : ℕ) (hk : 2 ≤ k) :
    ∃ (P : Program) (C b q : ℕ), 0 < C ∧ 0 < b ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (W : ℕ), requiredWidth b n ≤ W →
        ∃ t : ℕ, haltsListing P k G W t ∧
          t ≤ softBudget C q n (n ^ 2 + cycleCount G k) := by
  obtain ⟨P, C, b, q, hC, hb, hP⟩ := ram_listing k hk
  obtain ⟨E, hE⟩ := exploration_bound k hk
  refine ⟨P, C * (E + 1), b, q + 1, by positivity, hb, ?_⟩
  intro n G W hW
  obtain ⟨t, ht, htb⟩ := hP n G W hW
  refine ⟨t, ht, le_trans htb ?_⟩
  have hX := hE n G
  have hl : 1 ≤ logarithmicSize n := by unfold logarithmicSize; omega
  unfold softBudget
  set L := logarithmicSize n
  set s := n ^ 2 + cycleCount G k
  have h1 : 1 + (s + exploration G k) ≤ (E + 1) * (1 + s) * L := by
    have : exploration G k ≤ E * s * L := hX
    nlinarith
  calc C * (1 + (s + exploration G k)) * L ^ q
      ≤ C * ((E + 1) * (1 + s) * L) * L ^ q := by gcongr
    _ = C * (E + 1) * (1 + s) * L ^ (q + 1) := by ring
