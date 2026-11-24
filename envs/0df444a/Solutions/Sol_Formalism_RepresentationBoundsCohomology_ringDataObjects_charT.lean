-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.charT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:32:19.635775+00:00
-- url     : https://prove2.me/submissions/c5b8a7e9-ce3c-4c78-9da8-17bfca768f32

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_RingDataObjects
import Definitions.Def_Formalism_TruncatedSeriesCounting_TruncatedSeriesProofs_LemmaDetPoly
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_CMemPolyT
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_lift_mem
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_detT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical Polynomial
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
theorem _root_.solution : StatCharT := by
  intro O _ X T d _ _ G _ r hG1 a ha k
  have hA : (fun x => (a x).map C) ∈ spanSub (polyT T) (rPoly r) := lift_mem T r ha
  have hM : (fun x => 1 - (Polynomial.X : O[X]) • (a x).map C) ∈ spanSub (polyT T) (rPoly r) := by
    have he : (fun x => 1 - (Polynomial.X : O[X]) • (a x).map C) =
        1 - algebraMap O[X] (X → Matrix d d O[X]) Polynomial.X * (fun x => (a x).map C) := by
      funext x
      simp [Algebra.algebraMap_eq_smul_one, smul_mul_assoc]
    rw [he]
    exact Subalgebra.sub_mem _ (Subalgebra.one_mem _)
      (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hA)
  exact detT T r hG1 _ hM k
end Formalism.RepresentationBoundsCohomology.ringDataObjects
