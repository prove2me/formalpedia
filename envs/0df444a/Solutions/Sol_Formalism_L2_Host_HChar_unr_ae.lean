-- Prove2me | solution 1 for Formalism.L2.Host.HChar.unr_ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:39:57.043705+00:00
-- url     : https://prove2.me/submissions/0188bd43-33a0-4970-bc25-b0ab20cd98ef

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_UnrAe

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
variable {L : Type} [Field L] [NumberField L]
namespace Formalism.L2.Host
namespace HChar
theorem _root_.solution (h : UnrAE L) (χ : HChar L) : ∀ᶠ v in Filter.cofinite, χ.UnrAt v := by
  have hc : Continuous (χ.1 : Ideles L →* ℂˣ) := χ.2.1
  exact (h χ.1 hc).mono fun v hv x hx => hv x hx
end HChar
end Formalism.L2.Host
