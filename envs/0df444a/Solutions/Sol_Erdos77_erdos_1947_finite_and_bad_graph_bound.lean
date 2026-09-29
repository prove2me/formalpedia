-- Prove2me | solution 1 for Erdos77.erdos_1947_finite_and_bad_graph_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T10:45:49.350593+00:00
-- url     : https://prove2.me/submissions/7cbf15ba-4a63-4827-b3f3-8d2c2a959b95

import Definitions.Def_Erdos77_diagonal_ramsey
import Theorems.Thm_Erdos77_spencer_1975_finite_and_bad_graph_bound

theorem solution (k : Nat) (hk : 3 <= k)
    (hfinite : Exists fun n : Nat => forall G : SimpleGraph (Fin n),
      Or
        (Exists fun s : Finset (Fin n) => And (s.card = k) (G.IsClique s))
        (Exists fun s : Finset (Fin n) => And (s.card = k) ((Compl.compl G).IsClique s)))
    (hbad : Exists fun G : SimpleGraph (Fin (Nat.floor ((2 : Real) ^ ((k : Real) / 2)))) =>
      And
        (Not (Exists fun s : Finset (Fin (Nat.floor ((2 : Real) ^ ((k : Real) / 2)))) =>
          And (s.card = k) (G.IsClique s)))
        (Not (Exists fun s : Finset (Fin (Nat.floor ((2 : Real) ^ ((k : Real) / 2)))) =>
          And (s.card = k) ((Compl.compl G).IsClique s)))) :
    (2 : Real) ^ ((k : Real) / 2) < (Erdos77.diagonalRamsey k : Real) := by
  let n := Nat.floor ((2 : Real) ^ ((k : Real) / 2))
  rcases hbad with ⟨G, hG, hGc⟩
  have hbad' : Exists fun G : SimpleGraph (Fin n) =>
      And (Not (Exists fun s : Finset (Fin n) => And (s.card = k) (G.IsClique s)))
      (Not (Exists fun s : Finset (Fin n) => And (s.card = k) ((Compl.compl G).IsClique s))) := by
    exact ⟨G, hG, hGc⟩
  have hR := Erdos77.spencer_1975_finite_and_bad_graph_bound k n hfinite hbad'
  have hfloor : (2 : Real) ^ ((k : Real) / 2) < (n : Real) + 1 := by
    dsimp [n]
    exact Nat.lt_floor_add_one _
  exact hfloor.trans_le hR
