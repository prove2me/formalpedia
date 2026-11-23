-- Prove2me | solution 1 for Formalism.ELL.ExponentialCoefficientWeight.mul_le_strict
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:14:38.323475+00:00
-- url     : https://prove2.me/submissions/f862fc58-2d74-4cd5-a77f-442dc33fef74

import Definitions.Def_Formalism_EllipticTorsion_UnitCancel
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExpWeight

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
theorem _root_.solution {f g : PowerSeries K} {r A B : ℝ} (hr : 0 ≤ r) (hA : 0 ≤ A)
    (hB : 0 ≤ B) {n : ℕ} (hf0 : constantCoeff f = 0) (hg0 : constantCoeff g = 0)
    (hf : ∀ d < n, ‖coeff d f‖ ≤ A * r ^ d) (hg : ∀ d < n, ‖coeff d g‖ ≤ B * r ^ d) :
    ‖coeff n (f * g)‖ ≤ (A * B) * r ^ n := by
  rw [coeff_mul]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro x hx
  have hx : x.1 + x.2 = n := by simpa using hx
  rcases Nat.eq_zero_or_pos x.1 with h1 | h1
  · rw [h1, coeff_zero_eq_constantCoeff_apply, hf0, zero_mul, norm_zero]; positivity
  rcases Nat.eq_zero_or_pos x.2 with h2 | h2
  · rw [h2, coeff_zero_eq_constantCoeff_apply, hg0, mul_zero, norm_zero]; positivity
  rw [norm_mul, ← hx, pow_add]
  have e1 := hf x.1 (by omega)
  have e2 := hg x.2 (by omega)
  calc ‖coeff x.1 f‖ * ‖coeff x.2 g‖ ≤ (A * r ^ x.1) * (B * r ^ x.2) :=
        mul_le_mul e1 e2 (norm_nonneg _) (by positivity)
    _ = A * B * (r ^ x.1 * r ^ x.2) := by ring
end Formalism.ELL.ExponentialCoefficientWeight
