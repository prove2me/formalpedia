-- Prove2me | solution 1 for Formalism.L2.Fam.IdTrans.unrAe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:57:59.675801+00:00
-- url     : https://prove2.me/submissions/a7274180-3f45-4a7b-84e5-41947202c254

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_UnrAe
import Definitions.Def_Formalism_LocalToGlobal_NumberFieldFamilies_IdTransSM
import Theorems.Thm_Formalism_L2_Fam_IdTrans_unrAE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Filter Topology
open Formalism Formalism.L2 Formalism.L2.Fam Formalism.L2.Fam.IdTrans
namespace Formalism.L2.Fam.IdTrans
theorem _root_.solution {L : Type} [Field L] [NumberField L] (χ : HChar L) : ∀ᶠ v in cofinite, χ.UnrAt v := (unrAE (L := L) χ.1 χ.2.1).mono fun v hv x hx => hv x hx
end Formalism.L2.Fam.IdTrans
