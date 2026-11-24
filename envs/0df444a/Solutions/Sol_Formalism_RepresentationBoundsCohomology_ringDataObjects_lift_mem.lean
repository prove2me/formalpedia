-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.lift_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:41.808331+00:00
-- url     : https://prove2.me/submissions/37d30e72-7f8b-4d15-880e-83393cb745c2

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_RingDataObjects
import Definitions.Def_Formalism_TruncatedSeriesCounting_TruncatedSeriesProofs_LemmaDetPoly
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_CMemPolyT
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_C_mem_polyT

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
variable {O : Type} [CommRing O] {Xs : Type} (T : Subalgebra O (Xs → O))
  {d : Type} [Fintype d] [DecidableEq d] {G : Type} [Group G] (r : G →* (Xs → Matrix d d O))
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
theorem _root_.solution {a : Xs → Matrix d d O} (ha : a ∈ tSpan T r) :
    (fun x => (a x).map C) ∈ tSpan (polyT T) (rPoly r) := by
  obtain ⟨s, c, hc, rfl⟩ := ha
  refine ⟨s, fun g x => C (c g x), fun g => C_mem_polyT T (hc g), ?_⟩
  funext x
  ext i j
  simp [rPoly, Finset.sum_apply, Matrix.sum_apply, map_sum]
end Formalism.RepresentationBoundsCohomology.ringDataObjects
