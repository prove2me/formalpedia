-- Prove2me | solution 1 for Formalism.L2.Host.HChar.productRule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:28:42.37001+00:00
-- url     : https://prove2.me/submissions/18b86d22-bd19-4265-a668-51fbca7ad9fe

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_HeckeProd
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_CharProd
import Theorems.Thm_hecke_product_rule


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
open Formalism Formalism.L2 Formalism.L2.Host Formalism.L2.Host.HChar
variable {L : Type} [Field L] [NumberField L] (χ : HChar L)
namespace Formalism.L2.Host.HChar
theorem _root_.solution : χ.ProductRule := hecke_product_rule L χ
end Formalism.L2.Host.HChar
