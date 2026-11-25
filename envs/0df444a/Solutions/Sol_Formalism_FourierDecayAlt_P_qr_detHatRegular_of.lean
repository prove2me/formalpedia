-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.qr_detHatRegular_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:14:32.321772+00:00
-- url     : https://prove2.me/submissions/5fffe76b-01e7-4e1a-b5a6-e006e760fdbc

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameEntries
import Theorems.Thm_Formalism_FourierDecayAlt_P_FrameEntries_regular_smooth

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
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution (h : Formalism.FourierDecayAlt.Q.DetHat) : Formalism.FourierDecayAlt.Q.DetHatRegular := by
  intro k r z z' f hz hz' hT hT' hf
  exact h ℂ k r z z' Set.univ f hz hz' hT hT' isOpen_univ (FrameEntries.regular_smooth hf (Fin.last r) Set.univ)
end Formalism.FourierDecayAlt.P
