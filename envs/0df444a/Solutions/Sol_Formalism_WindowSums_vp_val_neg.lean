-- Prove2me | solution 1 for Formalism.WindowSums.vp_val_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:16.480746+00:00
-- url     : https://prove2.me/submissions/ef1f5150-2925-41ca-993c-694c72958e71

import Definitions.Def_Formalism_WindowSums_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ValProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.WindowSums
open Finset
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]
namespace Formalism.WindowSums
theorem _root_.solution (x : ℤ_[ℓ]) : (-x).valuation = x.valuation := by
  by_cases hx : x = 0
  · simp [hx]
  have h1 : (-1 : ℤ_[ℓ]) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hm1 : (-1 : ℤ_[ℓ]).valuation = 0 := by
    have h := PadicInt.valuation_mul h1 h1
    rw [neg_one_mul, neg_neg, PadicInt.valuation_one] at h
    omega
  rw [← neg_one_mul x, PadicInt.valuation_mul h1 hx, hm1, zero_add]
end Formalism.WindowSums
