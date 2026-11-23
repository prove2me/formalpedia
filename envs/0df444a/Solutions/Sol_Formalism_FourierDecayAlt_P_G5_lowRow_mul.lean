-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G5.lowRow_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:33.190372+00:00
-- url     : https://prove2.me/submissions/418366a4-b604-49be-9b04-0762de3037b5

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
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (a : Fin n → ℂ) :
    lowRow a * blk A 0 0 1 = blk A 0 (a ᵥ* A) 1 := by
  unfold lowRow
  rw [blk_mul]; simp
end Formalism.FourierDecayAlt.P.G5
