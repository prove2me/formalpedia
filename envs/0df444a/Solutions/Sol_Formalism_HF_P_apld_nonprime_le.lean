-- Prove2me | solution 1 for Formalism.HF.P.apld_nonprime_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:57.411901+00:00
-- url     : https://prove2.me/submissions/48fc393f-1fd0-4f2c-84ad-a6e5d65c9db2

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_APLogDensity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology ArithmeticFunction ArithmeticFunction.vonMangoldt Complex LSeries
noncomputable section
open Formalism Formalism.HF Formalism.HF.P
variable {q : ℕ} [NeZero q] {a : ZMod q}
namespace Formalism.HF.P
theorem _root_.solution (a : ZMod q) {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    (if n.Prime then 0 else residueClass a n) / (n : ℝ) ^ x ≤
      (if n.Prime then 0 else residueClass a n) / n := by
  split_ifs
  · simp
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [residueClass_apply_zero, zero_div, zero_div]
    · apply div_le_div_of_nonneg_left (residueClass_nonneg a n) (by exact_mod_cast hn)
      calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (n : ℝ) ^ x := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hx
end Formalism.HF.P
