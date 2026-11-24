-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.idemSmall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:36:42.174075+00:00
-- url     : https://prove2.me/submissions/cca124ca-cb5e-4186-bb7f-98d43f9c6fb6

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RightIdealImageOfSurjective
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GlobalModuleOf
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdempotentImageSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
theorem _root_.solution : StatIdemSmall := by
  unfold StatIdemSmall
  intro O _ _ _ n _ _ e he h0
  have h1 : (IsLocalRing.residue O).mapMatrix (1 - e) = 1 := by
    rw [map_sub, map_one, RingHom.mapMatrix_apply, h0, sub_zero]
  have hres : IsLocalRing.residue O (1 - e).det = 1 := by
    rw [RingHom.map_det, h1, Matrix.det_one]
  have hdet : IsUnit (1 - e).det := by
    by_contra hnu
    have hm : (1 - e).det ∈ IsLocalRing.maximalIdeal O := hnu
    rw [← IsLocalRing.residue_eq_zero_iff] at hm
    rw [hm] at hres
    exact zero_ne_one hres
  have hmul : e * (1 - e) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, he, sub_self]
  calc e = e * (1 - e) * (1 - e)⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
    _ = 0 := by rw [hmul, Matrix.zero_mul]
end Formalism.RepresentationBoundsCohomology.ringDataObjects
