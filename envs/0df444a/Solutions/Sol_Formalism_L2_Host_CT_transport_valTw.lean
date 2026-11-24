-- Prove2me | solution 1 for Formalism.L2.Host.CT.transport_valTw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:12:32.880589+00:00
-- url     : https://prove2.me/submissions/731c5455-f1cc-443f-8b71-45b184908e2e

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
theorem _root_.solution (j : E ≃+* L) (χ : HChar L) (s : ℝ) (w : HeightOneSpectrum (𝓞 E)) (h : χ.UnrAt (plMap j w)) :
    (transport j χ).valTw s w = χ.valTw s (plMap j w) := by
  unfold HChar.valTw
  rw [transport_val j χ w h, absNorm_plMap]
end Formalism.L2.Host.CT
