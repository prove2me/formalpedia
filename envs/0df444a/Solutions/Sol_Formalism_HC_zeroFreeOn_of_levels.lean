-- Prove2me | solution 1 for Formalism.HC.zeroFreeOn_of_levels
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:10.433817+00:00
-- url     : https://prove2.me/submissions/fb9e3360-7354-4c87-b8db-fc10392f0360

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Analytic
import Definitions.Def_Formalism_StatementOC
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions

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
theorem _root_.solution {Q : PChar → Prop} (h : ∀ ψ, Q ψ → ∃ Λ : Level, ψ ∈ Λ.KEPT ∧ Λ.ZeroFreeLevel) : ZeroFreeOn Q := by
  intro ψ hψ
  obtain ⟨Λ, h1, h2⟩ := h ψ hψ
  exact h2 ψ h1
end Formalism.HC
