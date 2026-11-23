-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsTorsion.mulz
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:09.543305+00:00
-- url     : https://prove2.me/submissions/df67a319-e808-4056-9007-9f627d57442e

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsTorsionFree
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsNoPrimeToPTorsion
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_add_le
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_add_lt
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_zfacts
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_key

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
open Formalism Formalism.ELL Formalism.ELL.FormalGroupPointsTorsion
open WeierstrassCurve Polynomial
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
variable {W : WeierstrassCurve K}
namespace Formalism.ELL.FormalGroupPointsTorsion
theorem _root_.solution [DecidableEq K] (hW : IntegralModel W) (P : W.toAffine.Point) (hP : InFormalGroupPoints P)
    (hP0 : P ≠ 0) (k : ℕ) :
    InFormalGroupPoints ((k + 1) • P) ∧ ‖zf ((k + 1) • P) - ((k + 1 : ℕ) : K) * zf P‖ < ‖zf P‖ := by
  have ht : 0 < ‖zf P‖ := by
    rcases P with _ | ⟨x, y, h⟩
    · exact absurd Affine.Point.zero_def.symm hP0
    · exact (zfacts hW h.1 hP).2.1
  induction k with
  | zero =>
    rw [zero_add, one_nsmul]
    refine ⟨hP, ?_⟩
    simpa using ht
  | succ k ih =>
    obtain ⟨hQ, hQz⟩ := ih
    rw [succ_nsmul]
    obtain ⟨hR, hRz⟩ := key hW _ P hQ hP (Or.inr hP0)
    refine ⟨hR, ?_⟩
    have hQn : ‖zf ((k + 1) • P)‖ ≤ ‖zf P‖ := by
      have : zf ((k + 1) • P) =
          (zf ((k + 1) • P) - ((k + 1 : ℕ) : K) * zf P) + ((k + 1 : ℕ) : K) * zf P := by ring
      rw [this]
      refine add_le hQz.le ?_
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one K _)
    rw [max_eq_right hQn] at hRz
    have : zf ((k + 1) • P + P) - ((k + 1 + 1 : ℕ) : K) * zf P =
        (zf ((k + 1) • P + P) - zf ((k + 1) • P) - zf P) +
          (zf ((k + 1) • P) - ((k + 1 : ℕ) : K) * zf P) := by
      push_cast; ring
    rw [this]
    exact add_lt hRz hQz
end Formalism.ELL.FormalGroupPointsTorsion
