-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.normSq_cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:36:09.964088+00:00
-- url     : https://prove2.me/submissions/5c8be342-6336-450a-ade0-a3cc1f4406ae

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleWordLengthLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZinvBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords
theorem _root_.solution : ContDiff ℝ ∞ (fun z : ℂ => Complex.normSq z) := by
  have h : (fun z : ℂ => Complex.normSq z) = fun z => ‖z‖ ^ 2 :=
    funext fun z => Complex.normSq_eq_norm_sq z
  rw [h]
  exact contDiff_norm_sq ℝ
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
