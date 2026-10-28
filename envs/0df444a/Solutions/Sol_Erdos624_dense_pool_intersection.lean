-- Prove2me | solution 1 for Erdos624.dense_pool_intersection
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T05:59:08.147047+00:00
-- url     : https://prove2.me/submissions/d7f84982-1f92-4b62-9322-732cf29b1ac3

import Mathlib
import Theorems.Thm_Erdos624_dense_pool_intersection_cleared
open Finset

theorem solution
    {U C : Type*} [Fintype U] [DecidableEq U] [DecidableEq C]
    (G : Finset C) (V : C → Finset U) (a q : ℕ)
    (ha : 1 ≤ a) (hq : 1 ≤ q) (hn : 1 ≤ Fintype.card U)
    (hPool : ∀ u ∈ G, a * #(V u) ≥ Fintype.card U)
    (hg : 2 * a * (q - 1) ≤ #G) :
    let b := 2 ^ (q + 1) * a ^ q
    let poolInter := fun (S : Finset C) =>
      (if h : S.Nonempty then S.inf' h V else (univ : Finset U))
    let good := {S ∈ G.powersetCard q | b * #(poolInter S) ≥ Fintype.card U}
    b * q.factorial * #good ≥ (#G) ^ q :=
  Erdos624.dense_pool_intersection_cleared G V a q ha hq hn hPool hg
