-- Prove2me | solution 1 for Formalism.L2.Host.CT.transport_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:23:58.745826+00:00
-- url     : https://prove2.me/submissions/8c04c329-4698-4f73-a027-20931ede12c5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_UnrAe
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_CharTransport
import Theorems.Thm_Formalism_L2_Host_CT_idMap_infDiag

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
open Formalism Formalism.L2 Formalism.L2.Host Formalism.L2.Host.CT
open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀
variable {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L]
namespace Formalism.L2.Host.CT
theorem _root_.solution (j : E ≃+* L) (χ : HChar L) (k : Eˣ) :
    (transport j χ).inf k = χ.inf (Units.map j.toMonoidHom k) := by
  exact congrArg χ.1 (idMap_infDiag j k)
end Formalism.L2.Host.CT
