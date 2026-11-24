-- Prove2me | solution 1 for Formalism.L2.Pj.DatLin.blk_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:15:49.411804+00:00
-- url     : https://prove2.me/submissions/2ea90fbd-a890-4b3c-beae-395f07005f01

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_DatMat
import Theorems.Thm_Formalism_L2_Pj_DatLin_blk_apply

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
theorem _root_.solution (N N' : ι → Matrix n n ℂ) : blk N ∘ₗ blk N' = blk (fun τ => N τ * N' τ) := by
  apply LinearMap.ext
  intro u
  funext τ
  simp only [LinearMap.comp_apply, blk_apply, Matrix.mulVec_mulVec]
end Formalism.L2.Pj.DatLin
