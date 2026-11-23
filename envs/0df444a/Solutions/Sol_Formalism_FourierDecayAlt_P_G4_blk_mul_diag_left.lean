-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G4.blk_mul_diag_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:39.999805+00:00
-- url     : https://prove2.me/submissions/7f76b3fa-f554-4a9f-9517-b8c199f581eb

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_blk_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_blk_inj

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
theorem _root_.solution {n : ℕ} (A K : Matrix (Fin n) (Fin n) ℂ) (b : Fin n → ℂ) :
    blk K 0 0 1 * blk A b 0 1 = blk (K * A) (K *ᵥ b) 0 1 := by
  rw [blk_mul, blk_inj]
  exact ⟨by simp, by simp, by simp, by simp⟩
end Formalism.FourierDecayAlt.P.G4
