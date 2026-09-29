-- Prove2me | solution 2 for Erdos77.erdos_1947_ramsey_finiteness
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T10:47:05.031989+00:00
-- url     : https://prove2.me/submissions/afc0eae9-4ca7-4871-ad76-194365ae84d5

import Mathlib
import Theorems.Thm_Erdos77_finite_asymmetric_ramsey

theorem solution (k : Nat) (hk : 1 <= k) :
    Exists fun n : Nat => forall G : SimpleGraph (Fin n),
      Or
        (Exists fun s : Finset (Fin n) => And (s.card = k) (G.IsClique s))
        (Exists fun s : Finset (Fin n) => And (s.card = k) ((Compl.compl G).IsClique s)) := by
  exact Erdos77.finite_asymmetric_ramsey k k hk hk