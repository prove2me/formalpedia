-- Prove2me | solution 1 for Formalism.L2.Pj.DatLin.trace_blk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:22:00.644947+00:00
-- url     : https://prove2.me/submissions/5a7600d5-93e3-4179-a89d-20ce10da7812

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_DatMat
import Theorems.Thm_Formalism_L2_Pj_DatLin_blk_eq_restrict
import Theorems.Thm_Formalism_L2_Pj_DatLin_trace_restrict_complex
import Theorems.Thm_Formalism_L2_Pj_DatLin_trace_blkC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.DatLin
open Matrix Complex
variable {ι n : Type} [Fintype ι] [Fintype n]
namespace Formalism.L2.Pj.DatLin
theorem _root_.solution [DecidableEq ι] [DecidableEq n] (N : ι → Matrix n n ℂ) :
    LinearMap.trace ℝ _ (blk N) = ∑ τ, 2 * (N τ).trace.re := by
  rw [blk_eq_restrict, trace_restrict_complex, trace_blkC, Complex.re_sum, Finset.mul_sum]
end Formalism.L2.Pj.DatLin
