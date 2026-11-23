-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vge_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:10.940237+00:00
-- url     : https://prove2.me/submissions/f9f07b7b-c81c-4a50-a222-9712e349a677

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vR_mul

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
theorem _root_.solution {a b : ℝ} {x y : K} (hx : vge v a x) (hy : vge v b y) : vge v (a + b) (x * y) := by
  unfold vge at *
  rw [vR_mul, WithTop.coe_add]
  exact add_le_add hx hy
end Formalism.MainNotions.PlaneGram
