-- Prove2me | solution 1 for Formalism.L2.Host.CT.transport_isUnitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:27:19.479166+00:00
-- url     : https://prove2.me/submissions/737fbdbf-5f08-4cfe-aca0-996d59f684bf

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
theorem _root_.solution (j : E ≃+* L) (χ : HChar L) (h : χ.IsUnitary) : (transport j χ).IsUnitary := by
  intro a
  exact h (idMap j a)
end Formalism.L2.Host.CT
