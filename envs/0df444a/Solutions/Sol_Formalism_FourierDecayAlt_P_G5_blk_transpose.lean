-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G5.blk_transpose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:19.22209+00:00
-- url     : https://prove2.me/submissions/1f94d102-5d15-4b59-b05c-468c95f6f104

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_blk_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_blk_cl
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_blk_lc
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_blk_ll

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
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) :
    (blk A b a e)ᵀ = blk Aᵀ a b e := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Matrix.transpose_apply, blk_cc, blk_cl, blk_lc, blk_ll]
end Formalism.FourierDecayAlt.P.G5
