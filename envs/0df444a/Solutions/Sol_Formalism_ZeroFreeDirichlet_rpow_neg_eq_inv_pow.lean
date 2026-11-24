-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.rpow_neg_eq_inv_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:45:08.775937+00:00
-- url     : https://prove2.me/submissions/ccc8970c-0a5c-456d-9dd2-4ec062a4f575

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ExcBoundOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (x ε : ℝ) (hx : 0 < x) (k : ℕ) (hk : 0 < k) :
    x ^ (-ε) = ((x ^ (ε / k)) ^ k)⁻¹ := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [← Real.rpow_mul_natCast hx.le, div_mul_cancel₀ ε hk', Real.rpow_neg hx.le]
end Formalism.ZeroFreeDirichlet
