-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.exists_saturated_matrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/84d307c0-fd46-414f-93fd-e9cebeeb94e4

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_card_badSaturationRows_lt_pow
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_exists_saturated_of_bad_row_union_bound

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (H m : ℕ) (hH : 2 ≤ H)
    (hm : 2 * (H : ℝ) * Real.log (H : ℝ) ≤ (m : ℝ)) :
    ∃ A : Fin (m * (m + 1) + 1) → (Fin m → Fin H) → Fin H,
      IsSaturated A := by
  classical
  let s := m * (m + 1) + 1
  let columnSets : Finset (Finset (Fin m → Fin H)) :=
    (Finset.univ : Finset (Fin m → Fin H)).powersetCard (m + 1)
  apply exists_saturated_of_bad_row_union_bound H m s
  have hterms : ∀ T ∈ columnSets,
      (badSaturationRows H m T).card ^ s ≤
        (H ^ (H ^ m - 1)) ^ s := by
    intro T hT
    have hcard : T.card = m + 1 :=
      (Finset.mem_powersetCard.mp hT).2
    exact Nat.pow_le_pow_left
      (card_badSaturationRows_lt_pow H m hH hm T hcard).le s
  have hnumber : columnSets.card ≤ (H ^ m) ^ (m + 1) := by
    dsimp [columnSets]
    simpa using Nat.choose_le_pow (H ^ m) (m + 1)
  have hpositive : 0 < H ^ m := pow_pos (show 0 < H by omega) _
  change
    (∑ T ∈ columnSets, (badSaturationRows H m T).card ^ s) <
      Fintype.card (Fin s → (Fin m → Fin H) → Fin H)
  calc
    (∑ T ∈ columnSets, (badSaturationRows H m T).card ^ s) ≤
        columnSets.card * (H ^ (H ^ m - 1)) ^ s := by
      calc
        (∑ T ∈ columnSets, (badSaturationRows H m T).card ^ s) ≤
            ∑ _T ∈ columnSets, (H ^ (H ^ m - 1)) ^ s := by
          exact Finset.sum_le_sum fun T hT => hterms T hT
        _ = columnSets.card * (H ^ (H ^ m - 1)) ^ s := by simp
    _ ≤ (H ^ m) ^ (m + 1) * (H ^ (H ^ m - 1)) ^ s :=
      Nat.mul_le_mul_right _ hnumber
    _ = H ^ (m * (m + 1) + (H ^ m - 1) * s) := by
      rw [← pow_mul, ← pow_mul, ← pow_add]
    _ < H ^ (H ^ m * s) := by
      apply Nat.pow_lt_pow_right (show 1 < H by omega)
      calc
        m * (m + 1) + (H ^ m - 1) * s <
            s + (H ^ m - 1) * s := by
          apply Nat.add_lt_add_right
          dsimp [s]
          omega
        _ = 1 * s + (H ^ m - 1) * s := by simp
        _ = (1 + (H ^ m - 1)) * s := by rw [Nat.add_mul]
        _ = H ^ m * s := by
          congr 1
          omega
    _ = Fintype.card (Fin s → (Fin m → Fin H) → Fin H) := by
      simp [← pow_mul]
end ErdosProblems.MulticolourTriangleRamsey
