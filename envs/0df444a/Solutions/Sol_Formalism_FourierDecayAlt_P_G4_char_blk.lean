-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G4.char_blk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:51.639806+00:00
-- url     : https://prove2.me/submissions/1ab38913-e8ad-4fae-ade4-76a03a434924

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_superSum_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_subSum_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_superSum_blk
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_subSum_blk

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
theorem _root_.solution : ∀ {n : ℕ} {k : Matrix (Fin n) (Fin n) ℂ}, IsUpperUni k →
    subSum (blk (wMat n * k⁻¹ * wMat n) 0 0 1) + superSum (blk k 0 0 1) = 0
  | 0, _, _ => by simp [subSum, superSum]
  | m + 1, k, hk => by
    rw [subSum_blk, superSum_blk, subSum_conj]
    simpa using superSum_inv hk
end Formalism.FourierDecayAlt.P.G4
