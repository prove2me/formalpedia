-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G5.wMat_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:55:59.483272+00:00
-- url     : https://prove2.me/submissions/50f7868b-6386-4b3c-bbfe-e6b639ec6f56

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G5
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.G5
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (wMat n * A) i j = A i.rev j := by
  simp [wMat, Matrix.mul_apply]
end Formalism.FourierDecayAlt.P.G5
