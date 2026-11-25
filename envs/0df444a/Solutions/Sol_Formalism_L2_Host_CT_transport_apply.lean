-- Prove2me | solution 1 for Formalism.L2.Host.CT.transport_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:18:47.177356+00:00
-- url     : https://prove2.me/submissions/a69a4729-c3ce-4dbf-b452-7db327e3549f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_UnrAe
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_CharTransport

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
theorem _root_.solution (j : E ≃+* L) (χ : HChar L) (a : Ideles E) : (transport j χ).1 a = χ.1 (idMap j a) := rfl
end Formalism.L2.Host.CT
