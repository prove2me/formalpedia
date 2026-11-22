-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.v_unit_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:06:36.175969+00:00
-- url     : https://prove2.me/submissions/296dd284-79c1-4586-9bb1-7986322755f7

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral

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
theorem _root_.solution {x : K} (h : v x = 0) : v x⁻¹ = 0 := by
  have hx : x ≠ 0 := by
    rintro rfl
    simp at h
  have := v.map_mul x x⁻¹
  rw [mul_inv_cancel₀ hx, AddValuation.map_one, h, zero_add] at this
  exact this.symm
end Formalism.MainNotions.PlaneGram
