-- Prove2me | solution 1 for EdmondsKarp.ShortestPath.run_isFlow
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T19:29:57.385427+00:00
-- url     : https://prove2.me/submissions/cf594d5b-5cd8-4fff-88d1-41b376be386e

import Definitions.Def_EdmondsKarp_ShortestPath_Run
import Theorems.Thm_EdmondsKarp_ShortestPath_augment_isFlow

open EdmondsKarp.ShortestPath

theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (K : ℕ) (f : ℕ → V → V → ℝ) (P : ℕ → List V) (hrun : IsShortestRun N K f P)
    (k : ℕ) (hk : k ≤ K) : IsFlow N (f k) := by
  induction k with
  | zero => exact hrun.1
  | succ k ih =>
    have hkK : k < K := by omega
    obtain ⟨hP, hnext⟩ := hrun.2 k hkK
    rw [hnext]
    exact (augment_isFlow N (f k) (P k) (ih (by omega)) hP.1).2.1
