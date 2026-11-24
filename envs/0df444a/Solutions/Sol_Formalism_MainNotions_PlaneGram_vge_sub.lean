-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vge_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:08:32.509555+00:00
-- url     : https://prove2.me/submissions/c03ddcc1-777b-461a-8773-04f5fc87d51c

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_add
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {a : ℝ} {x y : K} (hx : vge v a x) (hy : vge v a y) : vge v a (x - y) := by
  rw [sub_eq_add_neg]
  exact vge_add v hx (vge_neg v hy)
end Formalism.MainNotions.PlaneGram
