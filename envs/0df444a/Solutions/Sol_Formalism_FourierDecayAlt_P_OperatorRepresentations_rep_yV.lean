-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OperatorRepresentations.rep_yV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:38:49.114805+00:00
-- url     : https://prove2.me/submissions/a4055593-3737-4c6e-9443-5d959e5b4f4e

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_good_yv
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_rep_opV

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
theorem _root_.solution (hD : IsOpen D) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin (mdim k r i)) :
    Rep (yV k r z i D E c) (mulF fun g => yv k r z i g c) := rep_opV hD (good_yv z c)
end Formalism.FourierDecayAlt.P.OperatorRepresentations
