-- Prove2me | solution 1 for Formalism.REAL.indexArray_inner
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:43:48.426492+00:00
-- url     : https://prove2.me/submissions/2e97967e-13cb-44ca-bb68-a739fc2fa91a

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
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n j : ℕ}
namespace Formalism.REAL
theorem _root_.solution (F G : Arr V n j) : ⟪F, G⟫_ℂ = ∑ α, ⟪F α, G α⟫_ℂ := by
  exact PiLp.inner_apply F G
end Formalism.REAL
