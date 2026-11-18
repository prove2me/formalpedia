-- Prove2me | solution 1 for FasterDistributedMatching.ApproximateMatching.reusable_power_coloring
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:54:11.520605+00:00
-- url     : https://prove2.me/submissions/a238d306-9c25-40f6-92c1-069d9480d831

import Theorems.Thm_FasterDistributedMatching_ApproximateMatching_power_coloring
import Theorems.Thm_FasterDistributedMatching_ApproximateMatching_power_color_lift

open FasterDistributedMatching.ApproximateMatching

theorem solution :
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
  intro b
  obtain ⟨A,C,a,hC,ha,hT,hA⟩ := power_coloring b
  refine ⟨A,C,a,hC,ha,hT,?_⟩
  intro N G k ell hell hG ids hi
  obtain ⟨chi,hout,hproper⟩ := hA N G k ell hell hG ids hi
  have hl := power_color_lift N G ids hi.1 ell ((max 2 k.degree)^(a*ell)) chi hproper
  refine ⟨chi,hout,hproper,hl.1,?_⟩
  intro x q p hp pick hpick
  exact hl.2 p pick hpick
