-- Prove2me | solution 1 for Formalism.MainNotions.WeightedLatticeSum.sum_wt_int_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:52:21.127341+00:00
-- url     : https://prove2.me/submissions/2afc0fdb-4253-4ec2-962c-aa33225078fa

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_WeightedLatticeSum
import Theorems.Thm_Formalism_MainNotions_WeightedLatticeSum_sum_wt_le
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
private theorem sum_wt_natAbs_le_nine_mul_of_injOn (R : ℝ) (hR : 1 ≤ R) (s : Finset ℤ)
    (hinj : ∀ x ∈ s, ∀ y ∈ s, x.natAbs = y.natAbs → x = y) :
    ∑ a ∈ s, wt R a.natAbs ≤ 9 * R := by
  calc ∑ a ∈ s, wt R a.natAbs = ∑ m ∈ s.image Int.natAbs, wt R m :=
        (Finset.sum_image hinj).symm
    _ ≤ 9 * R := sum_wt_le R hR _
end Formalism.MainNotions.WeightedLatticeSum
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.WeightedLatticeSum
open Finset
namespace Formalism.MainNotions.WeightedLatticeSum
theorem _root_.solution (R : ℝ) (hR : 1 ≤ R) (S : Finset ℤ) : ∑ a ∈ S, wt R a.natAbs ≤ 18 * R := by
  have h1 := sum_wt_natAbs_le_nine_mul_of_injOn R hR (S.filter (fun a : ℤ => 0 ≤ a)) (by
    intro x hx y hy hxy
    have hx0 : 0 ≤ x := (Finset.mem_filter.mp hx).2
    have hy0 : 0 ≤ y := (Finset.mem_filter.mp hy).2
    have ex := Int.natAbs_eq x
    have ey := Int.natAbs_eq y
    rw [hxy] at ex
    omega)
  have h2 := sum_wt_natAbs_le_nine_mul_of_injOn R hR (S.filter (fun a : ℤ => ¬ 0 ≤ a)) (by
    intro x hx y hy hxy
    have hx0 : ¬ 0 ≤ x := (Finset.mem_filter.mp hx).2
    have hy0 : ¬ 0 ≤ y := (Finset.mem_filter.mp hy).2
    have ex := Int.natAbs_eq x
    have ey := Int.natAbs_eq y
    rw [hxy] at ex
    omega)
  calc ∑ a ∈ S, wt R a.natAbs
      = ∑ a ∈ S.filter (fun a : ℤ => 0 ≤ a), wt R a.natAbs +
          ∑ a ∈ S.filter (fun a : ℤ => ¬ 0 ≤ a), wt R a.natAbs :=
        (Finset.sum_filter_add_sum_filter_not S _ _).symm
    _ ≤ 9 * R + 9 * R := add_le_add h1 h2
    _ = 18 * R := by ring
end Formalism.MainNotions.WeightedLatticeSum
