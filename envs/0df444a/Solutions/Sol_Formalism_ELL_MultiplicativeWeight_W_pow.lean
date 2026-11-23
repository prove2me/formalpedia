-- Prove2me | solution 1 for Formalism.ELL.MultiplicativeWeight.W_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:21:54.071345+00:00
-- url     : https://prove2.me/submissions/c1484798-43c7-4251-b3d7-de86ae777468

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_CompExpWeight
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CompExp
import Theorems.Thm_Formalism_ELL_MultiplicativeWeight_W_one
import Theorems.Thm_Formalism_ELL_MultiplicativeWeight_W_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries IsUltrametricDist
universe u
open Formalism Formalism.ELL Formalism.ELL.MultiplicativeWeight
variable {K : Type*} [NormedField K] [IsUltrametricDist K] {σ : Type} (c : ℝ)
variable {c}
namespace Formalism.ELL.MultiplicativeWeight
theorem _root_.solution (hc : 0 < c) (hc1 : c ≤ 1) {w : ℤ} {f : MvPowerSeries σ K} (hf : W c w f) (n : ℕ) :
    W c (n * w) (f ^ n) := by
  induction n with
  | zero => simpa using W_one hc hc1
  | succ n ih => rw [pow_succ]; push_cast; rw [add_mul, one_mul]; exact W_mul hc ih hf
end Formalism.ELL.MultiplicativeWeight
