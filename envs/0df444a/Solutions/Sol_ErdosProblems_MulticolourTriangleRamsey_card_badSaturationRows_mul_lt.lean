-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.card_badSaturationRows_mul_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/5644fe0b-143e-497f-af5d-30240ffd4401

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_card_badSaturationRows_le
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_missing_symbol_power_bound_nat

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (H m : ℕ) (hH : 2 ≤ H)
    (hm : 2 * (H : ℝ) * Real.log (H : ℝ) ≤ (m : ℝ))
    (T : Finset (Fin m → Fin H)) (hT : T.card = m + 1) :
    (badSaturationRows H m T).card * H < H ^ (H ^ m) := by
  have hcolumns : m + 1 ≤ H ^ m := by
    calc
      m + 1 = T.card := hT.symm
      _ ≤ Fintype.card (Fin m → Fin H) := Finset.card_le_univ T
      _ = H ^ m := by simp
  have hremaining : 0 < H ^ (H ^ m - (m + 1)) := by
    exact pow_pos (show 0 < H by omega) _
  calc
    (badSaturationRows H m T).card * H ≤
        (H * ((H - 1) ^ T.card * H ^ (H ^ m - T.card))) * H :=
      Nat.mul_le_mul_right H (card_badSaturationRows_le H m T)
    _ = (H ^ 2 * (H - 1) ^ (m + 1)) *
          H ^ (H ^ m - (m + 1)) := by rw [hT]; ring
    _ < H ^ (m + 1) * H ^ (H ^ m - (m + 1)) :=
      Nat.mul_lt_mul_of_pos_right
        (missing_symbol_power_bound_nat H m hH hm) hremaining
    _ = H ^ (H ^ m) := by
      rw [← pow_add]
      congr 1
      omega
end ErdosProblems.MulticolourTriangleRamsey
