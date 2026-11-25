-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.act_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:28:28.680939+00:00
-- url     : https://prove2.me/submissions/e0cb7187-da90-4fda-aa1f-635c7966927a

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
theorem _root_.solution (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) (x' : X') (a : R')
    (v : EvalSp O d R' x') : a • v = fun i => ∑ j, a.1 x' i j • (v j : FractionRing O) := rfl
end Formalism.RepresentationBoundsCohomology.ringDataObjects
