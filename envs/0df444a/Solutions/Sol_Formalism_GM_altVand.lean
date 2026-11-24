-- Prove2me | solution 1 for Formalism.GM.altVand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:34.847296+00:00
-- url     : https://prove2.me/submissions/8b31886f-e3d2-49bc-ac93-dd38e303d6f7

import Definitions.Def_Formalism_MahlerMeasure_LevelSum
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Finset
namespace Formalism.GM
theorem _root_.solution (B : ℕ) : ∀ z l : ℕ,
    ∑ j ∈ range (l + 1), (-1 : ℚ) ^ j * (B.choose j : ℚ) * ((z + B + (l - j)).choose (l - j) : ℚ)
      = ((z + l).choose l : ℚ) := by
  induction B with
  | zero =>
    intro z l
    rw [Finset.sum_eq_single 0
      (fun j _ hj => by simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hj)]) (by simp)]
    simp
  | succ B ih =>
    intro z l
    cases l with
    | zero => simp
    | succ m =>
      have h1 := ih (z + 1) (m + 1)
      have h2 := ih (z + 1) m
      rw [Finset.sum_range_succ'] at h1 ⊢
      have key : ∀ j ∈ range (m + 1),
          (-1 : ℚ) ^ (j + 1) * ((B + 1).choose (j + 1) : ℚ) *
              ((z + (B + 1) + (m + 1 - (j + 1))).choose (m + 1 - (j + 1)) : ℚ) =
            (-1 : ℚ) ^ (j + 1) * (B.choose (j + 1) : ℚ) *
                ((z + 1 + B + (m + 1 - (j + 1))).choose (m + 1 - (j + 1)) : ℚ) -
              (-1 : ℚ) ^ j * (B.choose j : ℚ) * ((z + 1 + B + (m - j)).choose (m - j) : ℚ) := by
        intro j hj
        have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have e1 : z + (B + 1) + (m + 1 - (j + 1)) = z + 1 + B + (m - j) := by omega
        have e2 : m + 1 - (j + 1) = m - j := by omega
        have e3 : z + 1 + B + (m + 1 - (j + 1)) = z + 1 + B + (m - j) := by omega
        rw [e1, e3, e2, Nat.choose_succ_succ', Nat.cast_add, pow_succ]
        ring
      rw [Finset.sum_congr rfl key, Finset.sum_sub_distrib, h2]
      simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero] at h1 ⊢
      rw [show z + (B + 1) + (m + 1) = z + 1 + B + (m + 1) by omega]
      have hp : ((z + 1 + (m + 1)).choose (m + 1) : ℚ) =
          ((z + 1 + m).choose m : ℚ) + ((z + (m + 1)).choose (m + 1) : ℚ) := by
        have e1 : (z + 1 + (m + 1)).choose (m + 1) = (z + 1 + m + 1).choose (m + 1) := by
          rw [show z + 1 + (m + 1) = z + 1 + m + 1 by omega]
        have e2 : (z + (m + 1)).choose (m + 1) = (z + 1 + m).choose (m + 1) := by
          rw [show z + (m + 1) = z + 1 + m by omega]
        rw [e1, e2, Nat.choose_succ_succ']
        push_cast
        ring
      linear_combination h1 + hp
end Formalism.GM
