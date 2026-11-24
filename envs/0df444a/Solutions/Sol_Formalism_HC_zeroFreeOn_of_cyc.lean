-- Prove2me | solution 1 for Formalism.HC.zeroFreeOn_of_cyc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:26.384794+00:00
-- url     : https://prove2.me/submissions/0dd9f89f-a5a7-4e08-b77e-3686b87431d3

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Analytic
import Definitions.Def_Formalism_StatementOC
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Theorems.Thm_Formalism_HC_zeroFreeOn_of_levels
import Theorems.Thm_Formalism_HC_Level_mem_cyc

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
theorem _root_.solution {Q : PChar → Prop} (h : ∀ ψ, Q ψ → (Level.cyc ψ).ZeroFreeLevel) : ZeroFreeOn Q :=
  zeroFreeOn_of_levels fun ψ hψ => ⟨_, Level.mem_cyc ψ, h ψ hψ⟩
end Formalism.HC
