-- Prove2me | solution 1 for Formalism.ELL.ExponentialCoefficientWeight.pow_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:41.147319+00:00
-- url     : https://prove2.me/submissions/3411b01f-ff76-4001-b00e-7f81a993b52c

import Definitions.Def_Formalism_EllipticTorsion_UnitCancel
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExpWeight
import Theorems.Thm_Formalism_ELL_ExponentialCoefficientWeight_mul_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.ExponentialCoefficientWeight
variable {K : Type*} [NormedField K] [IsUltrametricDist K]
namespace Formalism.ELL.ExponentialCoefficientWeight
theorem _root_.solution {f : PowerSeries K} {r A : ℝ} (hr : 0 ≤ r) (hA : 0 ≤ A) {N : ℕ}
    (hf : ∀ d ≤ N, ‖coeff d f‖ ≤ A * r ^ d) :
    ∀ m : ℕ, ∀ d ≤ N, ‖coeff d (f ^ m)‖ ≤ A ^ m * r ^ d := by
  intro m
  induction m with
  | zero =>
    intro d hd
    rw [pow_zero, pow_zero, one_mul, coeff_one]
    split_ifs with h
    · subst h; simp
    · rw [norm_zero]; positivity
  | succ k ih =>
    intro d hd
    rw [pow_succ, pow_succ]
    exact mul_le hr (by positivity) hA ih hf d hd
end Formalism.ELL.ExponentialCoefficientWeight
