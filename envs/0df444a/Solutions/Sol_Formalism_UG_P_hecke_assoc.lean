-- Prove2me | solution 1 for Formalism.UG.P.hecke_assoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:42:21.179988+00:00
-- url     : https://prove2.me/submissions/1072948c-6d2a-4a44-ae0d-818238a49c99

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AssocFin
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeAssoc
import Theorems.Thm_Formalism_UG_P_conv_assoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {G : Type} [Group G] (K : Subgroup G)
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.HeckeAssoc := by
  intro G _ K k _ hK f₁ hf₁ f₂ hf₂ f₃ hf₃
  exact conv_assoc K hK f₁ f₂ f₃ hf₁.2 hf₂.1 hf₃.1 hf₃.2
end Formalism.UG.P
