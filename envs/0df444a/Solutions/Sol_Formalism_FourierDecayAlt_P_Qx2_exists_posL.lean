-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.exists_posL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:25:59.245118+00:00
-- url     : https://prove2.me/submissions/df01ee57-5d8e-4592-bcb8-d2ccf842a2dd

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
theorem _root_.solution {i : Fin (r + 1)} {p : Fin (2 * r + k + 1)} (hp : inV k r i p) :
    ∃ j, posL k r i j = p := by
  unfold inV at hp
  obtain ⟨h1, h2⟩ := hp
  have h3 := i.isLt
  refine ⟨⟨p.val - i.val, by unfold mdim; omega⟩, ?_⟩
  apply Fin.ext
  show p.val - i.val + i.val = p.val
  omega
end Formalism.FourierDecayAlt.P.Qx2
