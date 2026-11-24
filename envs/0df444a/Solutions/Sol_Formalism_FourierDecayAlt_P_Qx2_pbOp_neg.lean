-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.pbOp_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:24:55.006774+00:00
-- url     : https://prove2.me/submissions/73720686-952d-4a57-a73d-57d703d8fd3d

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
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ}
namespace Formalism.FourierDecayAlt.P.Qx2
theorem _root_.solution (l : Fin m) (f : (Fin m → ℂ) → E) : pbOp l (-f) = -pbOp l f := by
  funext x
  simp only [pbOp, wirtBar, Pi.neg_apply]
  rw [fderiv_neg]
  split_ifs <;> simp [smul_add, smul_neg, neg_add, add_comm]
end Formalism.FourierDecayAlt.P.Qx2
