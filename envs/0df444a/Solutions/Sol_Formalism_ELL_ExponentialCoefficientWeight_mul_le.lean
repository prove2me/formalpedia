-- Prove2me | solution 1 for Formalism.ELL.ExponentialCoefficientWeight.mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:10:03.212226+00:00
-- url     : https://prove2.me/submissions/06087fde-b150-4385-90fa-e9f671314baa

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
theorem _root_.solution {f g : PowerSeries K} {r A B : ℝ} (hr : 0 ≤ r) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {N : ℕ} (hf : ∀ d ≤ N, ‖coeff d f‖ ≤ A * r ^ d) (hg : ∀ d ≤ N, ‖coeff d g‖ ≤ B * r ^ d) :
    ∀ d ≤ N, ‖coeff d (f * g)‖ ≤ (A * B) * r ^ d := by
  intro d hd
  rw [coeff_mul]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro x hx
  have hx : x.1 + x.2 = d := by simpa using hx
  rw [norm_mul, ← hx, pow_add]
  have h1 := hf x.1 (by omega)
  have h2 := hg x.2 (by omega)
  calc ‖coeff x.1 f‖ * ‖coeff x.2 g‖ ≤ (A * r ^ x.1) * (B * r ^ x.2) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = A * B * (r ^ x.1 * r ^ x.2) := by ring
end Formalism.ELL.ExponentialCoefficientWeight
