-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G5.blk_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:53.51771+00:00
-- url     : https://prove2.me/submissions/a78371b8-1706-4ad5-a126-f7fd529e9763

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
theorem _root_.solution (n : ℕ) : blk (1 : Matrix (Fin n) (Fin n) ℂ) 0 0 1 = 1 := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [blk_cc, blk_cl, blk_lc, blk_ll, Matrix.one_apply, Fin.ext_iff, ne_of_gt, ne_of_lt]
end Formalism.FourierDecayAlt.P.G5
