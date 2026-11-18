-- Prove2me | solution 1 for FasterDistributedMatching.ApproximateMatching.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:39:03.20466+00:00
-- url     : https://prove2.me/submissions/cf899355-1d13-47dc-8526-f642214c9e7b

import Theorems.Thm_FasterDistributedMatching_ApproximateMatching_routed_simulation
import Theorems.Thm_FasterDistributedMatching_ApproximateMatching_line_simulation
import Theorems.Thm_FasterDistributedMatching_ApproximateMatching_reusable_power_coloring

open FasterDistributedMatching.ApproximateMatching

theorem solution :
    RoutedSimulation ∧ LineSimulation ∧
    ∀ b : ℕ, ∃ (A : Deterministic (Bounds × ℕ) (Finset ℕ) (ℕ → ℕ)) (C : ℝ) (a : ℕ),
      0 < C ∧ 1 ≤ a ∧
      (∀ k ell, 2 ≤ ell → A.program.rounds (k,ell) ≤ budget C (ell * (logStar k.n : ℝ))) ∧
      ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (k : Bounds) (ell : ℕ),
        2 ≤ ell → boundedGraph G k.n k.degree →
        ∀ ids : Fin N → ℕ, Identifiers k.n (b + 1) ids →
          ∃ chi : Sym2 (Fin N) → ℕ,
            (∀ u v, G.Adj u v →
              execute A G (k,ell) ids (neighborIDs G ids) u (ids v) = chi s(u,v) ∧
              execute A G (k,ell) ids (neighborIDs G ids) v (ids u) = chi s(u,v)) ∧
            Proper (graphPower (lineGraph G) (256 * ell + 1))
              ((max 2 k.degree) ^ (a * ell)) (fun e => chi e.val) ∧
            (∃ D : Routed G G.edgeSet,
              D.graph = graphPower (lineGraph G) (256 * ell + 1) ∧
              (∀ e : G.edgeSet, D.owner e ∈ e.val) ∧ RouteLength D (256 * ell + 3)) ∧
            ∀ (x : Sym2 (Fin N) → ℝ) (q : ℝ) (p : Pairing N),
              ValidPairing G x q p → ∀ pick : Copy p → Fin N, CopyEdgeChoice G p pick →
                ReusableColors G ell (2 * (max 2 k.degree) ^ (a * ell)) (copyColor ids chi pick) := by
  exact ⟨routed_simulation,line_simulation,reusable_power_coloring⟩
