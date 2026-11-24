-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.hMat_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:07:36.266828+00:00
-- url     : https://prove2.me/submissions/823b487d-7487-4e1d-ac7a-92d7b822ed97

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
variable {K : Type} [Field K]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (r : ℕ) (a b : Fin r) :
    hMat K r a b ∈ (Polynomial.toLaurent : Polynomial (GenF K r) →+* LauF K r).range := by
  unfold hMat sDiag Formalism.MainNotions.G.gL Formalism.MainNotions.G.gLinv
  rw [Matrix.transpose_apply]
  simp only [Matrix.mul_apply, Matrix.map_apply]
  refine Subring.sum_mem _ fun k _ => ?_
  refine Subring.mul_mem _ ?_ (RingHom.mem_range.mpr ⟨Polynomial.C _, Polynomial.toLaurent_C _⟩)
  refine Subring.sum_mem _ fun l _ => Subring.mul_mem _
    (RingHom.mem_range.mpr ⟨Polynomial.C _, Polynomial.toLaurent_C _⟩) ?_
  simp only [Matrix.diagonal_apply]
  split_ifs <;> first
    | exact RingHom.mem_range.mpr ⟨Polynomial.X, Polynomial.toLaurent_X⟩
    | exact Subring.one_mem _
    | exact Subring.zero_mem _
end Formalism.MainNotions.PlaneGram
