-- Prove2me | solution 1 for EdmondsKarp.ShortestPath.resDist_monotone_run
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T20:16:08.476223+00:00
-- url     : https://prove2.me/submissions/73426840-d2f5-45c9-8db0-b8408c2f1daa

import Theorems.Thm_EdmondsKarp_ShortestPath_resDist_monotone

open EdmondsKarp.ShortestPath

theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (K : ℕ) (f : ℕ → V → V → ℝ) (P : ℕ → List V) (hrun : IsShortestRun N K f P)
    (k l : ℕ) (hkl : k ≤ l) (hl : l ≤ K) (u : V) :
    resDist N (f k) N.s u ≤ resDist N (f l) N.s u ∧
    resDist N (f k) u N.t ≤ resDist N (f l) u N.t := by
  revert hl
  induction l, hkl using Nat.le_induction with
  | base => exact fun _ => ⟨le_rfl, le_rfl⟩
  | succ l hkl ih =>
    intro hl
    have hprev := ih (by omega)
    have hnext := resDist_monotone N K f P hrun l (by omega) u
    exact ⟨hprev.1.trans hnext.1, hprev.2.trans hnext.2⟩
