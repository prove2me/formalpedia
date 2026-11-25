-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.finrank_range_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:34:52.497361+00:00
-- url     : https://prove2.me/submissions/7b031a9f-1daa-4546-ac0e-d40ef3084a47

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
theorem _root_.solution (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) (x' : X') (a : R') :
    Module.finrank (FractionRing O)
      (LinearMap.range (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') a)) =
      (a.1 x').rank := by
  show Module.finrank (FractionRing O) (LinearMap.range (a.1 x').mulVecLin) = _
  rfl
end Formalism.RepresentationBoundsCohomology.ringDataObjects
