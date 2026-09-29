-- Prove2me | solution 1 for Erdos77.finite_asymmetric_ramsey
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T11:56:41.262986+00:00
-- url     : https://prove2.me/submissions/c16b9229-304c-4257-8821-7a823c304062

import Mathlib
import Theorems.Thm_erdos_szekeres_asymmetric_graph_bound

theorem solution (r s : Nat) (hr : 1 <= r) (hs : 1 <= s) :
    Exists fun n : Nat => forall G : SimpleGraph (Fin n),
      Or
        (Exists fun t : Finset (Fin n) => And (t.card = r) (G.IsClique t))
        (Exists fun t : Finset (Fin n) => And (t.card = s) ((Compl.compl G).IsClique t)) := by
  let n := Nat.choose (r + s - 2) (r - 1)
  refine ⟨n, ?_⟩
  intro G
  have h := erdos_szekeres_asymmetric_graph_bound r s hr hs G
  rcases h with h | h
  · left
    rcases h with ⟨t, ht⟩
    exact ⟨t, ht.2, ht.1⟩
  · right
    rcases h with ⟨t, ht⟩
    exact ⟨t, ht.2, ht.1⟩
