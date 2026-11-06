-- Prove2me | solution 1 for BookProof.QgTruncationResolvent.momWindow_exhausts
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:49:49.150411+00:00
-- url     : https://prove2.me/submissions/f893e798-15ea-433d-987c-2344cfe155b2

import Definitions.Def_ChapterQgTruncationResolvent

open BookProof.QgTruncationResolvent
open Filter Topology
open BookProof.QgContinuumModeInstance

noncomputable section

theorem solution (F : Finset CMode) :
    ∀ᶠ n : ℕ in atTop, ∀ a ∈ F, a ∈ momWindow n := by
  rw [eventually_atTop]
  refine ⟨F.sup (fun a => ⌈momSq a.1⌉₊), ?_⟩
  intro n hn a ha
  change momSq a.1 ≤ (n : ℝ)
  have hbound : ⌈momSq a.1⌉₊ ≤ n :=
    (Finset.le_sup (f := fun a : CMode => ⌈momSq a.1⌉₊) ha).trans hn
  exact (Nat.le_ceil _).trans (by exact_mod_cast hbound)
