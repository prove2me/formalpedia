-- Prove2me | solution 1 for Formalism.L2.NCov.val_prime_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:09:05.762388+00:00
-- url     : https://prove2.me/submissions/2e75ca1f-1d3f-4d58-894c-11b5a6257de9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverVal
import Theorems.Thm_Formalism_L2_NCov_val_prime_eq_zero

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
theorem _root_.solution {l p : ℕ} (hl : l.Prime) (hp : p.Prime) (hne : p ≠ l) (hvl : 0 < v (l : F))
    (f : ℕ) : v ((p ^ f : ℕ) : F) = 0 := by
  rw [Nat.cast_pow, AddValuation.map_pow, val_prime_eq_zero v hl hp hne hvl, smul_zero]
end Formalism.L2.NCov
