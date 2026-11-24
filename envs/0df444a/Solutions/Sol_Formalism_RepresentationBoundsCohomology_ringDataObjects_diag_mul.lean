-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.diag_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:36:39.192342+00:00
-- url     : https://prove2.me/submissions/63587c13-e4ef-4d19-b0db-caf68f429b93

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_CMemPolyT
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_Normal
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_BurnsideMat
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SpacedProductLowerBound
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_RankDiagIte

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
variable {A : Type*} [CommRing A] {d : Type} [Fintype d] [DecidableEq d] {α : Type} [DecidableEq α]
  (bl : d → α)
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
theorem _root_.solution {M N : Matrix d d A} (hM : ∀ i j, bl i ≠ bl j → M i j = 0) (i : d)
    (hi : ∀ l, bl i = bl l → i = l) : (M * N) i i = M i i * N i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rw [hM i k (fun h => hk (hi k h).symm), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h
end Formalism.RepresentationBoundsCohomology.ringDataObjects
