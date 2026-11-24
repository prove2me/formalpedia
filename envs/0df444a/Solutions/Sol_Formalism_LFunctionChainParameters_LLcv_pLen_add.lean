-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LLcv.pLen_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:29:30.872605+00:00
-- url     : https://prove2.me/submissions/cf7e8a2f-ad8b-4944-b9be-077b913475ab

import Definitions.Def_Formalism_SizeWindowBrackets_LcvBaseChange
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_len_add
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_mono


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
variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]
namespace Formalism.LFunctionChainParameters.LLcv
theorem _root_.solution (p : Ideal R) [p.IsPrime] {A C B : Submodule R W} (hBC : B ≤ C) (hCA : C ≤ A) :
    pLen p A B = pLen p C B + pLen p A C :=
  indexBasic_len_add (localization₂ p B) (localization₂ p C) (localization₂ p A) (locBasic_locS_mono _ hBC)
    (locBasic_locS_mono _ hCA)
end Formalism.LFunctionChainParameters.LLcv
