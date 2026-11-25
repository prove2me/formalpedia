-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FrameEntries.lZ_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:45:09.527264+00:00
-- url     : https://prove2.me/submissions/fb98796c-817e-4c8c-8d4b-b72e23728beb

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameEntries
import Theorems.Thm_Formalism_FourierDecayAlt_P_FrameEntries_ldV_smul

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
open Formalism.FourierDecayAlt.P.FrameEntries
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.FrameEntries
theorem _root_.solution (Z : Mx k r) (c : ℂ) (f : Mx k r → E) :
    LZ (Hpk k r) Z (fun x => c • f x) = fun x => c • LZ (Hpk k r) Z f x := by
  funext x
  unfold LZ
  simp only [ldV_smul, smul_add]
  rw [smul_comm Complex.I c]
end Formalism.FourierDecayAlt.P.FrameEntries
