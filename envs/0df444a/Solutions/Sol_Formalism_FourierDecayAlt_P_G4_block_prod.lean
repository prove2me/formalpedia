-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G4.block_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:40:18.123239+00:00
-- url     : https://prove2.me/submissions/846f51ad-8b2c-48b5-a797-3922548137c0

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
theorem _root_.solution {n : ℕ} (t c : ℂ) (l' u' : Matrix (Fin n) (Fin n) ℂ) (α β : Fin n → ℂ) :
    blk l' 0 α 1 * ptBlock n t c * blk u' β 0 1 =
      blk (l' * (t • wMat n) * u') ((l' * (t • wMat n)) *ᵥ β) (α ᵥ* ((t • wMat n) * u'))
        ((α ᵥ* (t • wMat n)) ⬝ᵥ β + c) := by
  unfold ptBlock
  rw [blk_mul, blk_mul, blk_inj]
  exact ⟨by simp, by simp, by simp [Matrix.vecMul_vecMul], by simp⟩
end Formalism.FourierDecayAlt.P.G4
