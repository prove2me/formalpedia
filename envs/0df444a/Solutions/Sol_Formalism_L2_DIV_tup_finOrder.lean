-- Prove2me | solution 1 for Formalism.L2.DIV.tup_finOrder
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:28:20.9177+00:00
-- url     : https://prove2.me/submissions/f4bab650-bc75-4f4d-a278-264f4413eba9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Tuples
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Theorems.Thm_Formalism_L2_DIV_mem_tupGrp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism Formalism.L2 Formalism.L2.DIV
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {K : Type} [Field K] [NumberField K] [StarRing K] {S : Set ℕ}
namespace Formalism.L2.DIV
theorem _root_.solution (ξ : Tup F E K S) : IsOfFinOrder (ξ : Chr F E K) := ((mem_tupGrp (ξ : Chr F E K)).mp ξ.2).1.2.2
end Formalism.L2.DIV
