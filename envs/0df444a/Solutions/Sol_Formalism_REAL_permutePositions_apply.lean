-- Prove2me | solution 1 for Formalism.REAL.permutePositions_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:12.0427+00:00
-- url     : https://prove2.me/submissions/8971445f-c46e-4fef-8bee-c255dbc4bde6

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero

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
theorem _root_.solution (σ : Equiv.Perm (Fin j)) (F : Arr V n j) (α : Fin j → Fin n × Fin n) :
    permArr V n σ F α = F (fun i => α (σ i)) := by
  rfl
end Formalism.REAL
