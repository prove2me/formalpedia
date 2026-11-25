-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.commonNonzero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:22:48.071516+00:00
-- url     : https://prove2.me/submissions/13d3c57e-5910-4994-a577-5a5e21ea4db7

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
theorem _root_.solution : StatCommonNonzero := by
  unfold StatCommonNonzero
  intro O _ _ _ σ ι _ D hD
  classical
  have hprod : (∏ i, D i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hD i
  by_contra hcon
  push_neg at hcon
  apply hprod
  apply MvPolynomial.funext
  intro z
  obtain ⟨i, hi⟩ := hcon z
  rw [map_prod, map_zero]
  exact Finset.prod_eq_zero (Finset.mem_univ i) hi
end Formalism.RepresentationBoundsCohomology.ringDataObjects
