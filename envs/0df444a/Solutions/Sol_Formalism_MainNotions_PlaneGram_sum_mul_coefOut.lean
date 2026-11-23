-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.sum_mul_coefOut
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:28.487805+00:00
-- url     : https://prove2.me/submissions/7a1591bf-7a54-49c5-9784-dcda424d3156

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ}
  (out : L → Prop) [DecidablePred out]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (g : (L × Fin r →₀ ℕ) → MvPolynomial (L × Fin r) K)
    (F : MvPolynomial (L × Fin r) K) :
    ∑ μ ∈ F.support.image (eOut out), g μ * coefOut out μ F =
      ∑ α ∈ F.support, g (eOut out α) * monomial (eIn out α) (F.coeff α) := by
  unfold coefOut
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α hα => ?_
  simp_rw [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_image_of_mem _ hα)]
end Formalism.MainNotions.PlaneGram
