-- Prove2me | solution 1 for Formalism.L2.Host.unif_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:47:39.094051+00:00
-- url     : https://prove2.me/submissions/acdfc927-4ebc-4155-9908-360a651de052

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipB
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR nonZeroDivisors
open Formalism Formalism.L2 Formalism.L2.Host
variable (L : Type) [Field L] [NumberField L]
variable {L}
namespace Formalism.L2.Host
theorem _root_.solution (v : HeightOneSpectrum (𝓞 L)) : IsUnifAt v (atFin v (unif v)) :=
  Classical.choose_spec (exists_unif v)
end Formalism.L2.Host
