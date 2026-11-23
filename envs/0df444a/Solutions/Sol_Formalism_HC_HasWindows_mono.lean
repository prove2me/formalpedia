-- Prove2me | solution 1 for Formalism.HC.HasWindows.mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:33.316861+00:00
-- url     : https://prove2.me/submissions/0f1163b3-8b81-40a6-afca-6e5c6b64e514

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
namespace HasWindows
theorem _root_.solution {S S' : Set ℝ} {la x0 : ℝ} (h : HasWindows S la) (hS : ∀ x ≥ x0, x ∈ S → x ∈ S') :
    HasWindows S' la := by
  intro y
  obtain ⟨Y, hyY, hY⟩ := h (max y x0)
  exact ⟨Y, (le_max_left _ _).trans hyY,
    fun x h1 h2 => hS x ((le_max_right _ _).trans (hyY.trans h1)) (hY x h1 h2)⟩
end HasWindows
end Formalism.HC
