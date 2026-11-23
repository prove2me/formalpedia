-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G4.w_conj_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:13.328114+00:00
-- url     : https://prove2.me/submissions/bbd26335-32e5-4614-91b7-32641f629946

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_w_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_mul_w_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.FourierDecayAlt.G
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G4
namespace Formalism.FourierDecayAlt.P.G4
theorem _root_.solution {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    (wMat d * M * wMat d) i j = M i.rev j.rev := by
  rw [mul_w_apply, w_mul_apply]
end Formalism.FourierDecayAlt.P.G4
