-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.smul_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:19:57.068869+00:00
-- url     : https://prove2.me/submissions/4c6926f2-97f5-49ed-88ad-835c29fc44d8

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_RankDiagIte
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RightIdealImageOfSurjective
import Definitions.Def_Formalism_TruncatedSeriesCounting_TruncatedSeriesProofs_BridgeDet
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_IsUnitDetOfConst
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_FinrankRangeEq

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
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X' : Type}
  (T' : Subalgebra O (X' → O)) {d : Type} [Fintype d] [DecidableEq d] {G : Type} [Group G]
  (rK : G →* (X' → Matrix d d (FractionRing O)))
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
theorem _root_.solution (f : T') (a : spanSub T' rK) (y : X') :
    (letI := algRp T' rK; (f • a : spanSub T' rK)).1 y =
      algebraMap O (FractionRing O) (f.1 y) • a.1 y := by
  letI := algRp T' rK
  show ((scal T' rK f) * a).1 y = _
  rw [Subalgebra.coe_mul, Pi.mul_apply, scal_apply, smul_mul_assoc, one_mul]
end Formalism.RepresentationBoundsCohomology.ringDataObjects
