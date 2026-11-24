-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.setTies_deg_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:01.897096+00:00
-- url     : https://prove2.me/submissions/c150ecfa-e450-4ece-9b4e-52ace9061caa

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_LatticeTheoremOfDischarge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open MvPolynomial Finset Formalism.GM.M Formalism.GM
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution {N : ℕ} (LL : Letters N) (T : TieData) (n n' : Fin T.t → ℕ) (h : ∀ i, n i ≤ n' i) (x : Fin N) :
    (LL.setTies T n).deg x ≤ (LL.setTies T n').deg x := by
  unfold Letters.setTies
  dsimp only
  split_ifs with hx
  · exact h _
  · exact le_rfl
end Formalism.InvariantFactorPaths.PW
