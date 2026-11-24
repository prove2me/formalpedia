-- Prove2me | solution 1 for Formalism.UG.P.cartan_decomposition_unique_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:20:19.562818+00:00
-- url     : https://prove2.me/submissions/65ca7792-5ab4-4ba1-9cd5-3782da72efa1

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
import Theorems.Thm_Formalism_UG_P_cartan_unique_gen
import Theorems.Thm_Formalism_UG_P_cartan_mem_Ov
import Theorems.Thm_Formalism_UG_P_cartan_unif_ne_zero
import Theorems.Thm_Formalism_UG_P_cartan_unif_lt_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open IsDedekindDomain NumberField
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.CartanUnique := by
  unfold Formalism.UG.CartanUnique
  intro F _ _ v n ϖ _ hϖ a a' ha ha' k₁ hk₁ k₂ hk₂ h
  unfold diagPow at h
  exact cartan_unique_gen (Ov F v) Valued.v (cartan_mem_Ov F v) ϖ (cartan_unif_ne_zero F v ϖ hϖ)
    (cartan_unif_lt_one F v ϖ hϖ) a a' ha ha' k₁ hk₁ k₂ hk₂ h
end Formalism.UG.P
