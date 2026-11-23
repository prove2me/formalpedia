-- Prove2me | solution 1 for Formalism.HC.Level.FormBAt.mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:33.821762+00:00
-- url     : https://prove2.me/submissions/a25efbc4-b9da-48ca-bee8-9178775de221

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
open Formalism.HC.Level
variable (Λ : Level)
variable {Λ}
namespace Formalism.HC.Level
namespace FormBAt
theorem _root_.solution {la la' : ℝ} (h : Λ.FormBAt la) (hl : la ≤ la') : Λ.FormBAt la' := by
  unfold FormBAt at h ⊢
  intro θ h0 h1 hw
  apply h θ h0 h1
  intro y
  obtain ⟨Y, hyY, hY⟩ := hw (max y 1)
  refine ⟨Y, (le_max_left _ _).trans hyY, fun x hx1 hx2 => hY x hx1 (hx2.trans ?_)⟩
  exact Real.rpow_le_rpow_of_exponent_le ((le_max_right _ _).trans hyY) hl
end FormBAt
end Formalism.HC.Level
