-- Prove2me | solution 1 for Formalism.UG.P.finite_adele_split_off_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:24:08.277139+00:00
-- url     : https://prove2.me/submissions/d487b029-44a1-4d53-8baf-2dd833a9cf89

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Theorems.Thm_Formalism_UG_P_afsplitE_fst
import Theorems.Thm_Formalism_UG_P_afsplitE_snd_eq_one
import Theorems.Thm_Formalism_UG_P_afsplitE_level

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.AfSplitOff := by
  unfold AfSplitOff
  intro F E _ _ _ _ _ n _ _ σ J v
  exact ⟨↥(afsplitKer σ J v), inferInstance, (levelAf σ J).subgroupOf (afsplitKer σ J v), afsplitE σ J v,
    fun g => afsplitE_fst σ J v g, fun g => afsplitE_snd_eq_one σ J v g, afsplitE_level σ J v⟩
end Formalism.UG.P
