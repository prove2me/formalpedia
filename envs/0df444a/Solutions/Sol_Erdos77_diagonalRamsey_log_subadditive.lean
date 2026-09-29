-- Prove2me | solution 1 for Erdos77.diagonalRamsey_log_subadditive
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T12:03:23.461661+00:00
-- url     : https://prove2.me/submissions/2a735384-087c-47f4-a1b8-831b0689f959
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey
import Theorems.Thm_Erdos77_diagonalRamsey_mul_bound
import Theorems.Thm_Erdos77_diagonalRamsey_ge_one
open Filter Topology

theorem solution :
    And (Subadditive (fun k : Nat => Real.log (Erdos77.diagonalRamsey k : Real)))
      (And (forall k : Nat, 0 <= Real.log (Erdos77.diagonalRamsey k : Real))
        (Exists fun N : Nat => forall k : Nat, N <= k ->
          0 < (Erdos77.diagonalRamsey k : Real))) := by
  constructor
  · intro m n
    by_cases hm : m = 0
    · subst m
      simp [Erdos77.diagonalRamsey]
    · by_cases hn : n = 0
      · subst n
        simp [Erdos77.diagonalRamsey]
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        have hmul := Erdos77.diagonalRamsey_mul_bound m n hmpos hnpos
        have hRmNat := Erdos77.diagonalRamsey_ge_one m hmpos
        have hRnNat := Erdos77.diagonalRamsey_ge_one n hnpos
        have hsumpos : 0 < m + n := by omega
        have hRsumNat := Erdos77.diagonalRamsey_ge_one (m + n) hsumpos
        have hmulReal : (Erdos77.diagonalRamsey (m + n) : Real) ≤
            (Erdos77.diagonalRamsey m : Real) * (Erdos77.diagonalRamsey n : Real) := by
          exact_mod_cast hmul
        have hRsumPos : 0 < (Erdos77.diagonalRamsey (m + n) : Real) := by
          exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hRsumNat
        have hRmPos : 0 < (Erdos77.diagonalRamsey m : Real) := by
          exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hRmNat
        have hRnPos : 0 < (Erdos77.diagonalRamsey n : Real) := by
          exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hRnNat
        calc
          Real.log (Erdos77.diagonalRamsey (m + n) : Real) ≤
              Real.log ((Erdos77.diagonalRamsey m : Real) * (Erdos77.diagonalRamsey n : Real)) :=
            Real.log_le_log hRsumPos hmulReal
          _ = Real.log (Erdos77.diagonalRamsey m : Real) +
              Real.log (Erdos77.diagonalRamsey n : Real) := Real.log_mul hRmPos.ne' hRnPos.ne'
  constructor
  · intro k
    by_cases hk : k = 0
    · subst k
      simp [Erdos77.diagonalRamsey]
    · have hR := Erdos77.diagonalRamsey_ge_one k (Nat.pos_of_ne_zero hk)
      exact Real.log_nonneg (by exact_mod_cast hR)
  · refine ⟨1, ?_⟩
    intro k hk
    have hkpos : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one hk
    have hR := Erdos77.diagonalRamsey_ge_one k hkpos
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hR
