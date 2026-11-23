-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.le_val_of_le_pow_six
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:23.74487+00:00
-- url     : https://prove2.me/submissions/0ae99466-9553-4d0b-a66e-63ca7384e558

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ)) {σ : Type}
variable {v}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (x : K) (m n : ℕ) (hmn : 6 * m ≤ n)
    (h : ((n : ℕ) : WithTop ℚ) ≤ v (x ^ 6)) : ((m : ℕ) : WithTop ℚ) ≤ v x := by
  have h6 : v (x ^ 6) = 6 • v x := AddValuation.map_pow v x 6
  rw [h6] at h
  by_cases hv : v x = ⊤
  · rw [hv]
    exact le_top
  · obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hv
    rw [← hq] at h ⊢
    rw [← WithTop.coe_nsmul, ← WithTop.coe_natCast, WithTop.coe_le_coe, nsmul_eq_mul] at h
    rw [← WithTop.coe_natCast, WithTop.coe_le_coe]
    have h2 : ((6 * m : ℕ) : ℚ) ≤ n := by exact_mod_cast hmn
    push_cast at h h2
    linarith
end Formalism.MainNotions.PlaneGram
