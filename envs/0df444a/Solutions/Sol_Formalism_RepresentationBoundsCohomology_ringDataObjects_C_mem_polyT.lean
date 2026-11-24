-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.C_mem_polyT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:53.818275+00:00
-- url     : https://prove2.me/submissions/df4417c1-1bc2-4816-9677-cb89d9c2b39a

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_RingDataObjects
import Definitions.Def_Formalism_TruncatedSeriesCounting_TruncatedSeriesProofs_LemmaDetPoly
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_CMemPolyT

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
theorem _root_.solution {c : Xs → O} (hc : c ∈ T) : (fun x => C (c x)) ∈ polyT T := by
  show ∀ k, (fun x => (C (c x)).coeff k) ∈ T
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using hc
  · have h0 : (fun x => (C (c x)).coeff k) = 0 := by
      funext x
      simp [Polynomial.coeff_C, hk.ne']
    rw [h0]
    exact T.zero_mem
end Formalism.RepresentationBoundsCohomology.ringDataObjects
