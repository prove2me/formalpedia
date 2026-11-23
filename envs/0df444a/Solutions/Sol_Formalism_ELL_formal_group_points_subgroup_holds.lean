-- Prove2me | solution 1 for Formalism.ELL.formal_group_points_subgroup_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:31:07.930791+00:00
-- url     : https://prove2.me/submissions/77a36d06-261e-40c8-8d80-04cdd02253b1

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsTorsionFree
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsSubgroupHolds
import Theorems.Thm_Formalism_ELL_FormalGroupPointsSubgroup_addX_norm

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
theorem _root_.solution : Formalism.ELL.FormalGroupPointsSubgroup' := by
  intro K _ _ W hW _ P Q hP hQ
  refine ⟨?_, ?_⟩
  · rcases P with _ | @⟨x₁, y₁, h₁⟩
    · rw [show (Affine.Point.zero : W.toAffine.Point) = 0 from rfl, zero_add]; exact hQ
    rcases Q with _ | @⟨x₂, y₂, h₂⟩
    · rw [show (Affine.Point.zero : W.toAffine.Point) = 0 from rfl, add_zero]; exact hP
    by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
    · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2]
      trivial
    · rw [Affine.Point.add_some hxy]
      exact FormalGroupPointsSubgroup.addX_norm W hW h₁.1 h₂.1 hxy hP hQ
  · rcases P with _ | @⟨x, y, h⟩
    · trivial
    · simpa [InFormalGroupPoints] using hP
end Formalism.ELL
