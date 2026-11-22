-- Prove2me | solution 1 for Formalism.REAL.firstPositionSlice_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:02:46.728995+00:00
-- url     : https://prove2.me/submissions/d82e88c0-45e0-4f3a-bd49-160907a5e773

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
theorem _root_.solution (α' : Fin j → Fin n × Fin n) (F : Arr V n (j+1)) (β : Fin 1 → Fin n × Fin n) :
    sliceLin V n α' F β = F (Fin.cons (β 0) α') := by
  rfl
end Formalism.REAL
