-- Prove2me | solution 1 for Formalism.L2.NCov.nonneg_of_isIntegral_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:09:01.514035+00:00
-- url     : https://prove2.me/submissions/c166417e-a2b8-4784-be5d-9c61a9aed9bd

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverVal
import Theorems.Thm_Formalism_L2_NCov_nonneg_of_isIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.NCov
open Polynomial
variable {F : Type*} [Field F] (v : AddValuation F (WithTop ℤ))
namespace Formalism.L2.NCov
theorem _root_.solution {p : F} (hp : v p = 0) {y : F} {N : ℕ}
    (hy : IsIntegral ℤ (p ^ N * y)) : 0 ≤ v y := by
  have h := nonneg_of_isIntegral v hy
  rwa [AddValuation.map_mul, AddValuation.map_pow, hp, smul_zero, zero_add] at h
end Formalism.L2.NCov
