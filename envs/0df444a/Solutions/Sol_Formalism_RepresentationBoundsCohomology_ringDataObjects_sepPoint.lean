-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.sepPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:36:21.47823+00:00
-- url     : https://prove2.me/submissions/38126c55-3bcf-4c29-9f5e-65107513dfbf

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
theorem _root_.solution : StatSepPoint := by
  unfold StatSepPoint
  intro O _ _ X _ T hsep x
  classical
  have hy : ∀ y, ∃ g ∈ T, y ≠ x → g y = 0 ∧ g x ≠ 0 := by
    intro y
    by_cases hyx : y = x
    · exact ⟨1, T.one_mem, fun h => absurd hyx h⟩
    · obtain ⟨f, hf, hne⟩ := hsep x y (Ne.symm hyx)
      refine ⟨f - algebraMap O (X → O) (f y), T.sub_mem hf (T.algebraMap_mem _), fun _ => ⟨by simp, ?_⟩⟩
      simpa [sub_eq_zero] using hne
  choose g hgT hg using hy
  refine ⟨∏ y ∈ Finset.univ.erase x, g y, prod_mem fun y _ => hgT y, ?_, ?_⟩
  · rw [Finset.prod_apply, Finset.prod_ne_zero_iff]
    intro y hy
    exact (hg y (Finset.ne_of_mem_erase hy)).2
  · intro z hz
    rw [Finset.prod_apply]
    exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hz, Finset.mem_univ z⟩) (hg z hz).1
end Formalism.RepresentationBoundsCohomology.ringDataObjects
