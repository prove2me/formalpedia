-- Prove2me | solution 1 for Formalism.HN.HeightGram.rkK_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:27:12.614888+00:00
-- url     : https://prove2.me/submissions/61a50133-b758-41b9-9180-1380ccb8c9e3

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.HeightGram
variable {K : Type} [Field K] [NumberField K]
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HN.HeightGram
theorem _root_.solution {j : ℕ} (e : Fin j → V) (he : LinearIndependent K e) :
    rkK (Submodule.span (𝓞 K) (Set.range e)) = j := by
  unfold rkK
  rw [Submodule.span_span_of_tower, finrank_span_eq_card he, Fintype.card_fin]
end Formalism.HN.HeightGram
