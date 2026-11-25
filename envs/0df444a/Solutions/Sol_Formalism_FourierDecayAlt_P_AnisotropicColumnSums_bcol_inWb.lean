-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AnisotropicColumnSums.bcol_inWb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:32:36.160789+00:00
-- url     : https://prove2.me/submissions/3121c084-0f5b-4750-9ae4-8d87a6958170

import Definitions.Def_Formalism_HermitianCurvature_FrameMinor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums

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
open Formalism.FourierDecayAlt.P.AnisotropicColumnSums
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.AnisotropicColumnSums
theorem _root_.solution {x : Fin (2 * r + k + 1) → ℂ} {Bs : Fin k → Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x)
    (hB : IsFrameOf k r [x] Bs) (j : Fin (mdim k r (Fin.last r))) : inWb k r (bcol k r x Bs j) := by
  unfold bcol
  split_ifs
  · exact hB.1 _
  · exact hx
end Formalism.FourierDecayAlt.P.AnisotropicColumnSums
