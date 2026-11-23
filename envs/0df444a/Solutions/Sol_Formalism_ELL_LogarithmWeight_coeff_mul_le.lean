-- Prove2me | solution 1 for Formalism.ELL.LogarithmWeight.coeff_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:12.138436+00:00
-- url     : https://prove2.me/submissions/51b6ad88-368d-43d5-8cc1-aa5ff2adc3bd

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_UnitCancel
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_LogWeight
import Theorems.Thm_Formalism_ELL_LogarithmWeight_norm_sum_mul_le

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
open Formalism Formalism.ELL Formalism.ELL.LogarithmWeight
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.ELL.LogarithmWeight
theorem _root_.solution {f g : PowerSeries K} {c A B : ℝ} (hc : 0 < c) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ n, ‖coeff n f‖ * c ^ n ≤ A) (hg : ∀ n, ‖coeff n g‖ * c ^ n ≤ B) (n : ℕ) :
    ‖coeff n (f * g)‖ * c ^ n ≤ A * B := by
  rw [PowerSeries.coeff_mul]
  apply norm_sum_mul_le _ _ (pow_pos hc n) (mul_nonneg hA hB)
  intro x hx
  have hx : x.1 + x.2 = n := by simpa using hx
  rw [norm_mul, ← hx, pow_add]
  calc ‖coeff x.1 f‖ * ‖coeff x.2 g‖ * (c ^ x.1 * c ^ x.2)
      = (‖coeff x.1 f‖ * c ^ x.1) * (‖coeff x.2 g‖ * c ^ x.2) := by ring
    _ ≤ A * B := mul_le_mul (hf _) (hg _) (by positivity) hA
end Formalism.ELL.LogarithmWeight
