-- Prove2me | solution 1 for Formalism.ELL.RootExponentBounds.tb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:49.530257+00:00
-- url     : https://prove2.me/submissions/a7de0b1f-3434-4c7d-9f3c-6a0aa928f223

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_ChangeIntegral
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_Change

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.ELL Formalism.G
open Formalism Formalism.ELL Formalism.ELL.RootExponentBounds
universe u
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.ELL.RootExponentBounds
theorem _root_.solution {a r : K} (k n : ℕ) (ha : ‖a‖ ≤ 1) (hr : 1 ≤ ‖r‖) (hk : k ≤ n) :
    ‖a * r ^ k‖ ≤ ‖r‖ ^ n := by
  rw [norm_mul, norm_pow]
  calc ‖a‖ * ‖r‖ ^ k ≤ 1 * ‖r‖ ^ n :=
        mul_le_mul ha (pow_le_pow_right₀ hr hk) (by positivity) zero_le_one
    _ = _ := one_mul _
end Formalism.ELL.RootExponentBounds
