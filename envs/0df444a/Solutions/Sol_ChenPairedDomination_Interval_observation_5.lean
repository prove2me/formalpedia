-- Prove2me | solution 1 for ChenPairedDomination.Interval.observation_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:23:51.27951+00:00
-- url     : https://prove2.me/submissions/2a2160a4-e3e6-4b62-9793-6b1496a61be8

import Definitions.Def_ChenPairedDomination_Interval_PrefixData

open ChenPairedDomination.Interval

theorem solution
    {n : ℕ} (G : SimpleGraph (Fin n))
    (R : ChenPairedDomination.Interval.OrderedRepresentation G)
    (i j : Fin n) (hji : j < i) (hij : G.Adj i j) :
    ∀ k : Fin n, j < k → k ≤ i → G.Adj j k := by
  intro k hjk hki
  obtain ⟨x, hx_i, hx_j⟩ := (R.represents i j hji.ne').mp hij
  rw [R.represents j k hjk.ne]
  refine ⟨R.left k, ⟨R.ordered hjk.le, ?_⟩, ⟨le_rfl, R.nonempty k⟩⟩
  exact (R.ordered hki).trans (hx_i.1.trans hx_j.2)
