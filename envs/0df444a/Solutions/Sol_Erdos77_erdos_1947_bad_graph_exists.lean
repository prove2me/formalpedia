-- Prove2me | solution 1 for Erdos77.erdos_1947_bad_graph_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T10:56:34.525979+00:00
-- url     : https://prove2.me/submissions/fc5d5a9e-a063-49f5-ad26-ef330ebe74b9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Erdos77_erdos_1947_lll_bad_graph
import Theorems.Thm_Erdos77_erdos_1947_floor_spencer_bound

theorem solution (k : Nat) (hk : 3 <= k) :
    Exists fun G : SimpleGraph (Fin (Nat.floor ((2 : Real) ^ ((k : Real) / 2)))) =>
      And
        (Not (Exists fun s : Finset (Fin (Nat.floor ((2 : Real) ^ ((k : Real) / 2)))) =>
          And (s.card = k) (G.IsClique s)))
        (Not (Exists fun s : Finset (Fin (Nat.floor ((2 : Real) ^ ((k : Real) / 2)))) =>
          And (s.card = k) ((Compl.compl G).IsClique s))) := by
  by_cases hk3 : k = 3
  case pos =>
    subst k
    have hfloor : Nat.floor ((2 : Real) ^ ((3 : Real) / 2)) = 2 := by
      have hsqrtlo : (1 : Real) <= Real.sqrt 2 :=
        (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
      have hsqrthi : Real.sqrt 2 < (3 : Real) / 2 :=
        (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
      have hsq : Real.sqrt (2 : Real) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hcubeNat : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
        calc
          Real.sqrt 2 ^ 3 = Real.sqrt 2 * Real.sqrt 2 ^ 2 := by ring
          _ = 2 * Real.sqrt 2 := by rw [hsq]; ring
      have hcube : Real.sqrt 2 ^ (3 : Real) = 2 * Real.sqrt 2 := by
        rw [show (3 : Real) = (3 : Nat) by norm_num, Real.rpow_natCast]
        exact hcubeNat
      have hpowlo : (2 : Real) <= (2 : Real) ^ ((3 : Real) / 2) := by
        rw [Real.rpow_div_two_eq_sqrt 3 (by norm_num : (0 : Real) <= 2)]
        calc
          (2 : Real) <= 2 * Real.sqrt 2 := by nlinarith [hsqrtlo]
          _ = Real.sqrt 2 ^ (3 : Real) := hcube.symm
      have hpowhi : (2 : Real) ^ ((3 : Real) / 2) < 3 := by
        rw [Real.rpow_div_two_eq_sqrt 3 (by norm_num : (0 : Real) <= 2)]
        calc
          Real.sqrt 2 ^ (3 : Real) = 2 * Real.sqrt 2 := hcube
          _ < 3 := by nlinarith [hsqrthi]
      apply (Nat.floor_eq_iff (by positivity : 0 <= (2 : Real) ^ ((3 : Real) / 2))).2
      constructor
      · exact hpowlo
      · linarith
    refine ⟨⊥, ?_, ?_⟩
    · rintro ⟨s, hs, _⟩
      have hle : s.card <= Nat.floor ((2 : Real) ^ ((3 : Real) / 2)) := by
        simpa using Finset.card_le_univ s
      rw [hfloor] at hle
      omega
    · rintro ⟨s, hs, _⟩
      have hle : s.card <= Nat.floor ((2 : Real) ^ ((3 : Real) / 2)) := by
        simpa using Finset.card_le_univ s
      rw [hfloor] at hle
      omega
  case neg =>
    have hk4 : 4 <= k := by omega
    let n : Nat := Nat.floor ((2 : Real) ^ ((k : Real) / 2))
    rcases Erdos77.erdos_1947_floor_spencer_bound k hk4 with ⟨hkn, hcond⟩
    exact Erdos77.erdos_1947_lll_bad_graph k n (by omega) hkn hcond
