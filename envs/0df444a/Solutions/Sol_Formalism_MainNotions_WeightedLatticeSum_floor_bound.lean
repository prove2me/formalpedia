-- Prove2me | solution 1 for Formalism.MainNotions.WeightedLatticeSum.floor_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:08:35.798258+00:00
-- url     : https://prove2.me/submissions/4cd4bb32-cdb9-4dc6-b885-4ebff9cfa285

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_WeightedLatticeSum
import Theorems.Thm_Formalism_MainNotions_WeightedLatticeSum_rpow_neg_three_halves
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.MainNotions.WeightedLatticeSum
open Finset
private theorem rpow_neg_three_halves_anti_of_one_le {s t : ℝ} (hs : 1 ≤ s) (hst : s ≤ t) :
    t ^ (-(3 / 2 : ℝ)) ≤ s ^ (-(3 / 2 : ℝ)) := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  rw [rpow_neg_three_halves hs0, rpow_neg_three_halves ht0]
  apply one_div_le_one_div_of_le (mul_pos hs0 (Real.sqrt_pos.mpr hs0))
  exact mul_le_mul hst (Real.sqrt_le_sqrt hst) (Real.sqrt_nonneg _) ht0.le
private theorem natAbs_floor_sub_one_le_abs (y : ℝ) : ((⌊y⌋.natAbs : ℕ) : ℝ) - 1 ≤ |y| := by
  have h1 := Int.floor_le y
  have h2 := Int.lt_floor_add_one y
  rcases Int.natAbs_eq ⌊y⌋ with h | h
  · have e : ((⌊y⌋ : ℤ) : ℝ) = (((⌊y⌋.natAbs : ℕ) : ℤ) : ℝ) := congrArg (fun n : ℤ => (n : ℝ)) h
    rw [Int.cast_natCast] at e
    linarith [le_abs_self y]
  · have e' : ((⌊y⌋ : ℤ) : ℝ) = -((⌊y⌋.natAbs : ℕ) : ℝ) := by exact_mod_cast h
    linarith [neg_abs_le y]
end Formalism.MainNotions.WeightedLatticeSum
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.WeightedLatticeSum
open Finset
namespace Formalism.MainNotions.WeightedLatticeSum
theorem _root_.solution (R : ℝ) (hR : 1 ≤ R) (x : ℝ) :
    (max 1 (|x| / R)) ^ (-(3 / 2 : ℝ)) ≤ wt R (⌊2 * x⌋).natAbs := by
  have hR0 : 0 < R := by linarith
  have key : (((⌊2 * x⌋).natAbs : ℕ) : ℝ) - 1 ≤ 2 * |x| := by
    have h := natAbs_floor_sub_one_le_abs (2 * x)
    rwa [abs_mul, abs_two] at h
  unfold wt
  apply rpow_neg_three_halves_anti_of_one_le (le_max_left _ _)
  apply max_le_max le_rfl
  rw [div_le_div_iff₀ (by linarith) hR0]
  nlinarith
end Formalism.MainNotions.WeightedLatticeSum
