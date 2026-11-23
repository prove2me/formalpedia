-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_S_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:48.942832+00:00
-- url     : https://prove2.me/submissions/784580b9-9a32-4e0f-8732-00c2c270bc7b

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaRowStrictMono
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaNuAntitone

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (a p : Fin n) : qa_S m a p ≤ ∑ b : Fin n, m (b, p) := by
  unfold qa_S
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
end Formalism.InvariantFactorPaths.ColumnFamilies
