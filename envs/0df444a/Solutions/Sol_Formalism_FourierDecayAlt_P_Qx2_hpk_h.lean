-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.hpk_h
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:15:53.476269+00:00
-- url     : https://prove2.me/submissions/b53aaf75-144f-4f86-bc44-912292b94c7e

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
theorem _root_.solution : (Hpk k r)ᴴ = Hpk k r := by
  ext a b
  rw [Matrix.conjTranspose_apply]
  simp only [Hpk]
  split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | (simp; done) | omega
end Formalism.FourierDecayAlt.P.Qx2
