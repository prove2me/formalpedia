-- Prove2me | solution 1 for Formalism.MainNotions.MassRatioZetaBound.two_le_absNorm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:27.623801+00:00
-- url     : https://prove2.me/submissions/297bc704-c1be-4c0e-b497-cbcc0297743a

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBound
import Theorems.Thm_Formalism_MainNotions_MassRatioZetaBound_exists_prime_mem
import Theorems.Thm_Formalism_MainNotions_MassRatioZetaBound_absNorm_ge

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
theorem _root_.solution (P : Ideal (𝓞 K)) [P.IsMaximal] : 2 ≤ Ideal.absNorm P := by
  obtain ⟨l, hl, hlP⟩ := exists_prime_mem P
  exact hl.two_le.trans (absNorm_ge P hl hlP).2
end Formalism.MainNotions.MassRatioZetaBound
