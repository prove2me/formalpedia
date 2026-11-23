-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.substS_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:27.798831+00:00
-- url     : https://prove2.me/submissions/d429e42a-0573-4d3d-b763-eb8208627bf0

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_substS_monomial

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
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ} {R : Type} [CommRing R]
  (ι : K →+* R) (sg : L → Bool) (S : Finset L) (A B : Matrix (Fin r) (Fin r) R)
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (T : Subring (MvPolynomial (L × Fin r) R)) (hC : ∀ c : K, C (ι c) ∈ T)
    (F : MvPolynomial (L × Fin r) K)
    (h : ∀ α ∈ F.support, ∀ x ∈ α.support, subX sg S A B x ∈ T) : substS ι sg S A B F ∈ T := by
  rw [F.as_sum, map_sum]
  refine Subring.sum_mem _ fun α hα => ?_
  rw [substS_monomial]
  refine Subring.mul_mem _ (hC _) ?_
  exact Subring.prod_mem _ fun x hx => Subring.pow_mem _ (h α hα x hx) _
end Formalism.MainNotions.PlaneGram
