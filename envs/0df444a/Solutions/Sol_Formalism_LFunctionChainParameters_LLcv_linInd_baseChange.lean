-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LLcv.linInd_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:29:30.225125+00:00
-- url     : https://prove2.me/submissions/909d8fb7-cb93-45f5-bcc3-0b769a66e557

import Definitions.Def_Formalism_SizeWindowBrackets_LcvBaseChange
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds
import Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_span_baseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LLcv
open Formalism.HN Formalism.HermitianLatticesTheory Formalism.LFunctionChainParameters.slopeLatticeData
open scoped Matrix
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
namespace Formalism.LFunctionChainParameters.LLcv
theorem _root_.solution {j : ℕ} (e : Fin j → V) (he : LinearIndependent K e)
    (g : Matrix (Fin j) (Fin j) K) (hg : IsUnit g.det) :
    LinearIndependent K (fun a => ∑ c, g c a • e c) := by
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, span_baseChange e g hg]
  exact linearIndependent_iff_card_eq_finrank_span.1 he
end Formalism.LFunctionChainParameters.LLcv
