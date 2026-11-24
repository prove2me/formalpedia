-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OperatorRepresentations.good_ybv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:58:38.683799+00:00
-- url     : https://prove2.me/submissions/06668b40-c6e6-468b-854e-efe62e89cc27

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_good_mulF
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_smooth_ybv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.OperatorRepresentations
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.OperatorRepresentations
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) (c : Fin (mdim k r i)) :
    Qx2.Good k r i D (mulF (E := E) fun g => ybv k r z i g c) := good_mulF (smooth_ybv z c)
end Formalism.FourierDecayAlt.P.OperatorRepresentations
