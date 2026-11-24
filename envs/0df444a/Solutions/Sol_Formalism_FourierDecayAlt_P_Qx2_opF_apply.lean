-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.opF_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:24:19.731799+00:00
-- url     : https://prove2.me/submissions/d039d1f1-5908-422e-8091-e63c876d64cb

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
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.Qx2
theorem _root_.solution (Y : ℂ) (x : ℂ × Fin (mdim k r i) × Fin (mdim k r i)) (h : Mx k r → E) (g : Mx k r) :
    opF k r i Y x h g = dl k r i x • ((Y + x.1) • h g) + EH k r (posL k r i x.2.1) (posL k r i x.2.2) h g := by
  simp only [opF, dl, QuantumDeterminants.Top]
  split_ifs <;> simp
end Formalism.FourierDecayAlt.P.Qx2
