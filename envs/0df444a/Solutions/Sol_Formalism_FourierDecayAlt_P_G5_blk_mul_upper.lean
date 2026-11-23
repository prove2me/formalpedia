-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G5.blk_mul_upper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:45:45.989036+00:00
-- url     : https://prove2.me/submissions/dd9f5efa-7a15-44c7-b077-0bc18d7752aa

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_blk_mul

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
theorem _root_.solution {n : ℕ} (A A' : Matrix (Fin n) (Fin n) ℂ) (b b' : Fin n → ℂ) :
    blk A b 0 1 * blk A' b' 0 1 = blk (A * A') (A *ᵥ b' + b) 0 1 := by
  rw [blk_mul]; simp
end Formalism.FourierDecayAlt.P.G5
