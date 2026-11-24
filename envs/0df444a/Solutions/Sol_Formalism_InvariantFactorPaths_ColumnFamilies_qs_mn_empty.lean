-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_mn_empty
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:15.309678+00:00
-- url     : https://prove2.me/submissions/8060b021-bd3c-453a-b095-8a2f0aae00c9

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsRemIffAdd
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsSymDMatEq
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_mn_eq


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
variable {n : ℕ} [NeZero n]
omit [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {R : Type*} [CommRing R] (g : Matrix (Fin n) (Fin n) R) : qs_mn g ∅ ∅ = 1 := by
  rw [qs_mn_eq g ∅ ∅ (h := 0) rfl rfl]; simp
end Formalism.InvariantFactorPaths.ColumnFamilies
