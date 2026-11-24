-- Prove2me | solution 1 for Formalism.MainNotions.MassRatioZetaBound.summable_Z
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:41:41.542863+00:00
-- url     : https://prove2.me/submissions/58ad4319-dba0-431d-9dc0-fb26faf43e3c

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.MassRatioZetaBound
open NumberField
variable {K : Type*} [Field K] [NumberField K]
namespace Formalism.MainNotions.MassRatioZetaBound
theorem _root_.solution : Summable fun m : ℕ => 1 / (m : ℝ) ^ ((3 : ℝ) / 2) :=
  Real.summable_one_div_nat_rpow.2 (by norm_num)
end Formalism.MainNotions.MassRatioZetaBound
