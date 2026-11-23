-- Prove2me | solution 1 for Formalism.ELL.formal_group_points_no_prime_to_p_torsion
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:39:46.263255+00:00
-- url     : https://prove2.me/submissions/38f4b1ab-2d9c-465d-8d7c-2ecba6891689

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsTorsionFree
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsNoPrimeToPTorsion
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_mulz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open Formalism Formalism.ELL
open WeierstrassCurve
open Classical
namespace Formalism.ELL
theorem _root_.solution : FormalGroupPointsTorsionFree.{u} := by
  intro K _ _ W hW _ n hn P hP hnP
  by_contra hP0
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero (by rintro rfl; simp at hn)
  have h := (FormalGroupPointsTorsion.mulz hW P hP hP0 m).2
  rw [hnP, Affine.Point.zero_def] at h
  simp only [FormalGroupPointsTorsion.zf, zero_sub, norm_neg, norm_mul, hn, one_mul] at h
  exact lt_irrefl _ h
end Formalism.ELL
