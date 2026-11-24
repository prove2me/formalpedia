-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_typeSum_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:37:06.227601+00:00
-- url     : https://prove2.me/submissions/b5f7eb8d-4454-4db1-8061-4fbf6570154c

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsEqLattice
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_FiltrationTypeIntersection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (M : GLMod n) {pi pi' : Set (Fin n → ℤ)} (h : pi ⊆ pi') : typeSum M pi ≤ typeSum M pi' :=
  Submodule.span_mono (by
    rintro _ ⟨mu, hmu, v, hv, g, rfl⟩
    exact ⟨mu, h hmu, v, hv, g, rfl⟩)
end Formalism.InvariantFactorPaths.ColumnFamilies
