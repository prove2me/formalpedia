-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.card_badSaturationRows_lt_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/55278b3e-b33b-4abd-a83d-e6cd8b1f406d

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_card_badSaturationRows_mul_lt

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (H m : ℕ) (hH : 2 ≤ H)
    (hm : 2 * (H : ℝ) * Real.log (H : ℝ) ≤ (m : ℝ))
    (T : Finset (Fin m → Fin H)) (hT : T.card = m + 1) :
    (badSaturationRows H m T).card < H ^ (H ^ m - 1) := by
  have hpositive : 0 < H ^ m := pow_pos (show 0 < H by omega) _
  have hpower : H ^ (H ^ m) = H ^ (H ^ m - 1) * H := by
    rw [← pow_succ]
    congr 1
    omega
  have hrows := card_badSaturationRows_mul_lt H m hH hm T hT
  rw [hpower] at hrows
  exact (Nat.mul_lt_mul_right (show 0 < H by omega)).mp hrows
end ErdosProblems.MulticolourTriangleRamsey
