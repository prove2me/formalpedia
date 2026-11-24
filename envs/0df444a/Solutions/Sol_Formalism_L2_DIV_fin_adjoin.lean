-- Prove2me | solution 1 for Formalism.L2.DIV.fin_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:05:03.355117+00:00
-- url     : https://prove2.me/submissions/d86d9a92-db86-4418-9787-94a390757e61

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ConjugationAtDistinguishedPlace
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoeffLemmas
import Theorems.Thm_Formalism_L2_DIV_isIntegralQb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.L2.Host Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution {S : Set Qb} (hS : S.Finite) : FiniteDimensional ℚ (adjoin ℚ S) := by
  have : Finite S := hS
  exact finiteDimensional_adjoin fun x _ => isIntegralQb x
end Formalism.L2.DIV
