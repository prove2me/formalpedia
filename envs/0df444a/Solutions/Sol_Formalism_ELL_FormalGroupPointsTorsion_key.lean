-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsTorsion.key
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:31:56.630801+00:00
-- url     : https://prove2.me/submissions/d159458b-dd6e-470e-b1fd-a2b9f82b8758

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsTorsionFree
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsNoPrimeToPTorsion
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_zfacts
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_negz
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_chord

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
theorem _root_.solution [DecidableEq K] (hW : IntegralModel W) (P Q : W.toAffine.Point) (hP : InFormalGroupPoints P)
    (hQ : InFormalGroupPoints Q) (hne : P ≠ 0 ∨ Q ≠ 0) :
    InFormalGroupPoints (P + Q) ∧ ‖zf (P + Q) - zf P - zf Q‖ < max ‖zf P‖ ‖zf Q‖ := by
  rcases P with _ | ⟨x1, y1, h1⟩ <;> rcases Q with _ | ⟨x2, y2, h2⟩
  · rw [← Affine.Point.zero_def] at hne; simp at hne
  · have hz : (Affine.Point.zero : W.toAffine.Point) + .some x2 y2 h2 = .some x2 y2 h2 := by
      rw [← Affine.Point.zero_def, zero_add]
    rw [hz]
    refine ⟨hQ, ?_⟩
    obtain ⟨-, ht, -, -⟩ := zfacts hW h2.1 hQ
    simp only [zf, sub_zero, sub_self, norm_zero]
    exact lt_max_of_lt_right ht
  · have hz : .some x1 y1 h1 + (Affine.Point.zero : W.toAffine.Point) = .some x1 y1 h1 := by
      rw [← Affine.Point.zero_def, add_zero]
    rw [hz]
    refine ⟨hP, ?_⟩
    obtain ⟨-, ht, -, -⟩ := zfacts hW h1.1 hP
    simp only [zf, sub_zero, sub_self, norm_zero]
    exact lt_max_of_lt_left ht
  · by_cases hxy : x1 = x2 ∧ y1 = W.toAffine.negY x2 y2
    · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2, Affine.Point.zero_def]
      refine ⟨trivial, ?_⟩
      simp only [zf, zero_sub]
      rw [hxy.1, hxy.2]
      have : -(x2 / W.toAffine.negY x2 y2) - x2 / y2 = -(x2 / W.toAffine.negY x2 y2 + x2 / y2) := by
        ring
      rw [this, norm_neg]
      have hng := negz hW h2.1 hQ
      obtain ⟨-, ht, ht', -⟩ := zfacts hW h2.1 hQ
      have : ‖x2 / y2‖ ^ 2 < ‖x2 / y2‖ := by nlinarith
      exact (hng.trans_lt this).trans_le (le_max_right _ _)
    · rw [Affine.Point.add_some hxy]
      exact chord hW h1.1 h2.1 hP hQ hxy
end Formalism.ELL.FormalGroupPointsTorsion
