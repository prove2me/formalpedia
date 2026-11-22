-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_colH_high
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:38:26.321801+00:00
-- url     : https://prove2.me/submissions/4870a7f9-c057-40c4-a07b-a51413a7beb1

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsRemIffAdd
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsSymDMatEq
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh

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
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {mu : Fin n → ℤ} (hmu : Dominant mu) {c : ℤ} (hc : mu 0 < c) : colH mu c = 0 := by
  unfold colH
  rw [Finset.filter_false_of_mem (fun m _ => by have := hmu (Fin.zero_le m); omega)]; simp
end Formalism.InvariantFactorPaths.ColumnFamilies
