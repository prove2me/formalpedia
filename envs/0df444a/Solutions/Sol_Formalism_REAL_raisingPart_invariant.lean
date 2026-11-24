-- Prove2me | solution 1 for Formalism.REAL.raisingPart_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:44:09.989744+00:00
-- url     : https://prove2.me/submissions/40bca9ad-a726-4d6c-ba41-046bc87ac617

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
import Theorems.Thm_Formalism_REAL_compactSpan_invariant
import Theorems.Thm_Formalism_REAL_kStable_iSup_iSup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ}
namespace Formalism.REAL
theorem _root_.solution (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ)
    (u : V) : KStable ε (arrE E 1) (Vplus ε E Λ u) := by
  unfold Vplus isoPart
  exact kStable_iSup_iSup ε (arrE E 1) _ fun y _ => compactSpan_invariant ε (arrE E 1) y
end Formalism.REAL
