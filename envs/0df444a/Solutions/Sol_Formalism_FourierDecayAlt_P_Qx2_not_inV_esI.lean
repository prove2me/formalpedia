-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.not_inV_esI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:25:00.531801+00:00
-- url     : https://prove2.me/submissions/8328ef80-31d5-4677-b59e-a182a7581be0

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.Qx2
theorem _root_.solution {i : Fin (r + 1)} {a : Fin r} (ha : a.val < i.val) : ¬ inV k r i (esI k r a) := by
  intro h
  unfold inV at h
  have h1 := h.2
  change 2 * r + k - a.val + i.val ≤ 2 * r + k at h1
  have := a.isLt
  omega
end Formalism.FourierDecayAlt.P.Qx2
