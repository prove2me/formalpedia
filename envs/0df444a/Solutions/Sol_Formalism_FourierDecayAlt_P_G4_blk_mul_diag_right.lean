-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G4.blk_mul_diag_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:07.922979+00:00
-- url     : https://prove2.me/submissions/7fa8620c-5a1b-4abd-895a-7f7693b714d0

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
theorem _root_.solution {n : ℕ} (A K : Matrix (Fin n) (Fin n) ℂ) (a : Fin n → ℂ) :
    blk A 0 a 1 * blk K 0 0 1 = blk (A * K) 0 (a ᵥ* K) 1 := by
  rw [blk_mul, blk_inj]
  exact ⟨by simp, by simp, by simp, by simp⟩
end Formalism.FourierDecayAlt.P.G4
