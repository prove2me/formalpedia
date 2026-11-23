-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G4.lowerUni_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:13:26.872312+00:00
-- url     : https://prove2.me/submissions/9fc356e1-edf2-49ba-bfbe-786f1353f354

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_w_conj_apply

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
theorem _root_.solution {d : ℕ} {u : Matrix (Fin d) (Fin d) ℂ} (hu : IsUpperUni u) :
    IsLowerUni (wMat d * u * wMat d) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [transpose_apply, w_conj_apply]; exact hu.1 _
  · rw [transpose_apply, w_conj_apply]; exact hu.2 _ _ (Fin.rev_lt_rev.2 hij)
end Formalism.FourierDecayAlt.P.G4
