-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_domLE_trans
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:37:23.812897+00:00
-- url     : https://prove2.me/submissions/45085e0b-1ee0-4754-8a73-c37d9e36bf0b

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreW

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
theorem _root_.solution {a b c : Fin n → ℤ} (h1 : DomLE a b) (h2 : DomLE b c) : DomLE a c :=
  ⟨fun i => (h1.1 i).trans (h2.1 i), h1.2.trans h2.2⟩
end Formalism.InvariantFactorPaths.ColumnFamilies
