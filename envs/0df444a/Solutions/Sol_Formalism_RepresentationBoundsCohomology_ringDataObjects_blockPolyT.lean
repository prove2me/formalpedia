-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.blockPolyT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:28:44.467771+00:00
-- url     : https://prove2.me/submissions/e570e971-1d2d-4fc5-907b-f7ef8c1bfd0f

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
theorem _root_.solution : StatBlockPolyT := by
  intro O _ X T d _ _ G _ r hG1 e he a ha k
  have hE : (fun x => (e x).map C) ∈ spanSub (polyT T) (rPoly r) := lift_mem T r he
  have hA : (fun x => (a x).map C) ∈ spanSub (polyT T) (rPoly r) := lift_mem T r ha
  have hM : (fun x => (Polynomial.X : O[X]) • (e x).map C - (a x).map C + (1 - e x).map C) ∈
      spanSub (polyT T) (rPoly r) := by
    have hq : (fun x => (Polynomial.X : O[X]) • (e x).map C - (a x).map C + (1 - e x).map C) =
        algebraMap O[X] (X → Matrix d d O[X]) Polynomial.X * (fun x => (e x).map C) -
          (fun x => (a x).map C) + (1 - fun x => (e x).map C) := by
      funext x
      ext i j
      by_cases h : i = j
      · subst h
        simp [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, Matrix.one_apply]
      · simp [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, Matrix.one_apply, h]
    rw [hq]
    exact Subalgebra.add_mem _ (Subalgebra.sub_mem _
      (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hE) hA)
      (Subalgebra.sub_mem _ (Subalgebra.one_mem _) hE)
  exact detT T r hG1 _ hM k
end Formalism.RepresentationBoundsCohomology.ringDataObjects
