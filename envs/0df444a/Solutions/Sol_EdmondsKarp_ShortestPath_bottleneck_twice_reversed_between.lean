-- Prove2me | solution 1 for EdmondsKarp.ShortestPath.bottleneck_twice_reversed_between
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T19:19:25.323978+00:00
-- url     : https://prove2.me/submissions/b5bf090f-2905-4715-8063-c88ea14f5530

import Theorems.Thm_EdmondsKarp_ShortestPath_bottleneck_not_residual_next
import Theorems.Thm_EdmondsKarp_ShortestPath_residual_next_sub

open EdmondsKarp.ShortestPath

theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (K : ℕ) (f : ℕ → V → V → ℝ) (P : ℕ → List V) (hrun : IsShortestRun N K f P)
    (k m : ℕ) (hkm : k < m) (hmK : m < K) (u v : V)
    (hbk : IsBottleneck N (f k) (P k) u v) (hbm : IsBottleneck N (f m) (P m) u v) :
    ∃ l, k < l ∧ l < m ∧ (v, u) ∈ pathArcs (P l) := by
  by_contra hn
  push_neg at hn
  have hnone : ∀ n, k < n → n ≤ m → ¬ ResArc N (f n) u v := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
      intro hkn hnm hres
      by_cases hnk : n = k
      · subst n
        exact bottleneck_not_residual_next N K f P hrun k (by omega) u v hbk hres
      · have hklt : k < n := by omega
        rcases residual_next_sub N K f P hrun n (by omega) u v hres with h | h
        · exact ih hklt (by omega) h
        · exact hn n hklt (by omega) h
  exact hnone m hkm le_rfl ((hrun.2 m hmK).1.1.2.2.2 (u, v) hbm.1)
