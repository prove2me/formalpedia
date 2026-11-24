-- Prove2me | solution 1 for Bl.general_b_fact_right_bis_other.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:40.796011+00:00
-- url     : https://prove2.me/submissions/230f4bba-5365-4352-9049-4f8fc88842d6

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRightBisAlt_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open Bl Bl.general_b_fact_right_bis_other
namespace Bl.general_b_fact_right_bis_other
theorem _root_.solution :
  ∀ {K : Type u_1} [inst : CommRing.{u_1} K] {n : Nat} {l l' : Matrix.{0, 0, u_1} (Fin n) (Fin n) K},
  (∀ (a b : Fin n), LT.lt.{0} a b → Eq.{u_1 + 1} (l a b) 0) →
    (∀ (a b : Fin n), LT.lt.{0} a b → Eq.{u_1 + 1} (l' a b) 0) →
      ∀ (a : Fin n), Eq.{u_1 + 1} (HMul.hMul.{u_1, u_1, u_1} l l' a a) (HMul.hMul.{u_1, u_1, u_1} (l a a) (l' a a)) := by
  intro K _ n l l' hl hl' a
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single a ?_ ?_
  · intro c _ hca
    rcases lt_or_gt_of_ne hca with h | h
    · rw [hl' c a h, mul_zero]
    · rw [hl a c h, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a) h
end Bl.general_b_fact_right_bis_other
