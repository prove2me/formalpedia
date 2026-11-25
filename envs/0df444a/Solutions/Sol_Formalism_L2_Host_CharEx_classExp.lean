-- Prove2me | solution 1 for Formalism.L2.Host.CharEx.classExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:55:42.424396+00:00
-- url     : https://prove2.me/submissions/4d941ec9-7d72-46fb-a80d-481212f29b2e

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_CharExGen
import Theorems.Thm_Formalism_L2_Host_CharEx_mem_unitIdeles_iff
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_classOf_eq_one_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open Formalism Formalism.L2 Formalism.L2.Host
open Formalism.L2.Host.CharEx
variable (L : Type) [Field L] [NumberField L]
namespace Formalism.L2.Host.CharEx
theorem _root_.solution : ClassExp L := by
  refine ⟨Fintype.card (ClassGroup (𝓞 L)), Fintype.card_pos, fun x => ?_⟩
  have h1 : classOf L (x ^ Fintype.card (ClassGroup (𝓞 L))) = 1 := by
    rw [map_pow, pow_card_eq_one]
  obtain ⟨k, u, hu, hx⟩ := (classOf_eq_one_iff L _).mp h1
  refine ⟨k⁻¹, ?_⟩
  rw [hx, map_inv, mul_comm (diagUnits L k) u, mul_inv_cancel_right]
  exact (mem_unitIdeles_iff L u).mpr hu
end Formalism.L2.Host.CharEx
