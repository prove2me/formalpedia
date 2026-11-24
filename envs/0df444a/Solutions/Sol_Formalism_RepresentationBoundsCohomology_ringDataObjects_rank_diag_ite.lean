-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.rank_diag_ite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:36:46.187809+00:00
-- url     : https://prove2.me/submissions/644c2455-3985-4a52-bb8b-5dd75109c674

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
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
theorem _root_.solution {K : Type*} [Field K] {d : Type} [Fintype d] [DecidableEq d] (S : d → Prop)
    [DecidablePred S] :
    (Matrix.diagonal fun a => if S a then (1 : K) else 0).rank = Nat.card {a // S a} := by
  rw [Matrix.rank_diagonal, Nat.card_eq_fintype_card]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun a => by by_cases h : S a <;> simp [h])
end Formalism.RepresentationBoundsCohomology.ringDataObjects
