-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.unit_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:24:58.760913+00:00
-- url     : https://prove2.me/submissions/c164dfcc-70ef-4553-a564-1fba7046621c

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
theorem _root_.solution {i : Fin (r + 1)} {a b p : Fin (2 * r + k + 1)} (hb : inV k r i b) (hp : ¬ inV k r i p) :
    (Matrix.single a b (1 : ℂ) : Mx k r) *ᵥ bvec p = 0 := by
  have hbp : b ≠ p := fun e => hp (e ▸ hb)
  ext q
  simp [bvec, Matrix.mulVec, dotProduct, Matrix.single_apply, Pi.single_apply, hbp]
end Formalism.FourierDecayAlt.P.Qx2
