-- Prove2me | solution 1 for Erdos77.erdos_1947_lll_bad_graph
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T11:54:40.878735+00:00
-- url     : https://prove2.me/submissions/c77cf508-8df7-4a43-89cb-808da42b9796
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Erdos77_spencer_1975_lll_bad_graph_criterion_fintype

theorem solution (k n : Nat) (hk : 2 <= k) (hkn : k <= n)
    (hcond : (4 : Real) * (Nat.choose k 2 : Real) * (Nat.choose (n - 2) (k - 2) : Real) *
      (2 : Real) ^ (1 - (Nat.choose k 2 : Real)) < 1) :
    Exists fun G : SimpleGraph (Fin n) =>
      And
        (Not (Exists fun s : Finset (Fin n) => And (s.card = k) (G.IsClique s)))
        (Not (Exists fun s : Finset (Fin n) =>
          And (s.card = k) ((Compl.compl G).IsClique s))) := by
  have hkn' : k <= Fintype.card (Fin n) := by simpa using hkn
  have hcond' :
      (4 : Real) * (Nat.choose k 2 : Real) *
          (Nat.choose (Fintype.card (Fin n) - 2) (k - 2) : Real) *
          (2 : Real) ^ (1 - (Nat.choose k 2 : Real)) < 1 := by
    simpa using hcond
  exact Erdos77.spencer_1975_lll_bad_graph_criterion_fintype
    (V := Fin n) k hk hkn' hcond'
