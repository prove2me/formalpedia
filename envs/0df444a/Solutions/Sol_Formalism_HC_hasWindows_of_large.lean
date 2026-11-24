-- Prove2me | solution 1 for Formalism.HC.hasWindows_of_large
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:57.092878+00:00
-- url     : https://prove2.me/submissions/62d2c9c8-8382-4af1-a0d2-671804b48e66

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Window

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
theorem _root_.solution {S : Set ℝ} {x0 : ℝ} (h : ∀ x ≥ x0, x ∈ S) (la : ℝ) : HasWindows S la :=
  fun y => ⟨max y x0, le_max_left _ _, fun x h1 _ => h x ((le_max_right _ _).trans h1)⟩
end Formalism.HC
