-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G4.upperUni_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:13:28.2938+00:00
-- url     : https://prove2.me/submissions/213c83fb-baf0-47a7-a70b-1c583cb1424c

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
theorem _root_.solution {d : ℕ} {l : Matrix (Fin d) (Fin d) ℂ} (hl : IsLowerUni l) :
    IsUpperUni (wMat d * l * wMat d) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [w_conj_apply]; exact hl.1 _
  · rw [w_conj_apply]; exact hl.2 _ _ (Fin.rev_lt_rev.2 hij)
end Formalism.FourierDecayAlt.P.G4
