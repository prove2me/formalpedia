-- Prove2me | solution 1 for Formalism.HC.Level.mem_cyc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:50.775977+00:00
-- url     : https://prove2.me/submissions/906c1d4b-e1d5-4878-bbc5-1ba37a130a97

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Analytic
import Definitions.Def_Formalism_StatementOC
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Theorems.Thm_Formalism_HC_PChar_of_self
import Theorems.Thm_Formalism_HC_Level_mem_ofSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC
namespace Formalism.HC
namespace Level
theorem _root_.solution (ψ : PChar) : ψ ∈ (Level.cyc ψ).KEPT :=
  (Level.mem_ofSub _ _).2 ⟨ψ.χ, Subgroup.mem_zpowers _, ψ.of_self⟩
end Level
end Formalism.HC
