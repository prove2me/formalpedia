-- Prove2me | solution 1 for Formalism.UG.P.csAsm_hform_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:38:07.832877+00:00
-- url     : https://prove2.me/submissions/b9c922ff-d576-4319-b373-a38dc6d8d295

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LevelSubgroupFiniteAdelicStandard
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsAsmHformSmulRight

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
open Formalism.UG Formalism.UG.CS
namespace Formalism.UG.P
theorem _root_.solution {E : Type} [Field E] (σ : E →+* E) {n : Type} [Fintype n]
    (J : Matrix n n E) (c : E) (y x : n → E) :
    hform σ J y (c • x) = c * hform σ J y x := by
  unfold Formalism.UG.hform
  simp [Matrix.mulVec_smul, dotProduct_smul, Finset.mul_sum, smul_eq_mul, mul_left_comm]
end Formalism.UG.P
