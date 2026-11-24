-- Prove2me | solution 1 for Formalism.UG.P.hecke_algebra_GL_comm_of_cartan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:37:08.900164+00:00
-- url     : https://prove2.me/submissions/3f988c8e-e0be-462d-8216-a5b03d710de1

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeConvolutionMemHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckecomm
import Theorems.Thm_Formalism_UG_P_heckecomm_gelfand
import Theorems.Thm_Formalism_UG_P_heckecomm_tr_mul
import Theorems.Thm_Formalism_UG_P_heckecomm_tr_tr
import Theorems.Thm_Formalism_UG_P_heckecomm_tr_mem
import Theorems.Thm_Formalism_UG_P_heckecomm_tr_dc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
namespace Formalism.UG.P
theorem _root_.solution (hCartanDecomp : Formalism.UG.CartanDecomp) : Formalism.UG.HeckeCommGL := by
  intro F _ _ v n k _ f₁ hf₁ f₂ hf₂
  exact heckecomm_gelfand _ heckecomm_tr heckecomm_tr_mul heckecomm_tr_tr
    (heckecomm_tr_mem (Ov F v)) (heckecomm_tr_dc hCartanDecomp F v n) f₁ f₂ hf₁.1 hf₂.1
end Formalism.UG.P
