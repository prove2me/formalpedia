-- Prove2me | solution 2 for FamousTheorems.triangle_counting_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:55:56.928111+00:00
-- url     : https://prove2.me/submissions/e566852f-819d-4d2a-9541-6d707a6edc3c

import Mathlib

theorem solution {α : Type*} [DecidableEq α] [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj] {ε : ℝ} {s t u : Finset α}
    (dst : 2 * ε ≤ G.edgeDensity s t) (ust : G.IsUniform ε s t) (hst : Disjoint s t)
    (dsu : 2 * ε ≤ G.edgeDensity s u) (usu : G.IsUniform ε s u) (hsu : Disjoint s u)
    (dtu : 2 * ε ≤ G.edgeDensity t u) (utu : G.IsUniform ε t u) (htu : Disjoint t u) :
    (1 - 2 * ε) * ε ^ 3 * s.card * t.card * u.card ≤ (G.cliqueFinset 3).card :=
  G.triangle_counting dst ust hst dsu usu hsu dtu utu htu
