-- Prove2me | solution 1 for Bl.general_b_fact_upper.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:44.628911+00:00
-- url     : https://prove2.me/submissions/93502f86-85e5-4b2f-8e58-2b4ae21d8d7c

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactUpper_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_upper
namespace Bl.general_b_fact_upper
theorem _root_.solution :
  ∀ {K : Type} [inst : NormedField.{0} K] [IsUltrametricDist.{0} K] {x y : K},
  LE.le.{0} (Norm.norm.{0} x) 1 →
    LE.le.{0} (Norm.norm.{0} y) 1 →
      ∀ (n : Nat),
        LE.le.{0} (Norm.norm.{0} (HSub.hSub.{0, 0, 0} (HPow.hPow.{0, 0, 0} x n) (HPow.hPow.{0, 0, 0} y n)))
          (Norm.norm.{0} (HSub.hSub.{0, 0, 0} x y)) := by
  intro K _ _ x y hx hy n
  induction n with
  | zero => simp
  | succ n ih =>
    have e : x ^ (n + 1) - y ^ (n + 1) = x ^ n * (x - y) + (x ^ n - y ^ n) * y := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hx)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) hy).trans ih
end Bl.general_b_fact_upper
