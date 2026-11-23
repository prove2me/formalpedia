-- Prove2me | solution 1 for Formalism.ELL.MultiplicativeWeight.W_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:15.282531+00:00
-- url     : https://prove2.me/submissions/dd501a5c-0801-41eb-9077-6c1b78e7172f

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_CompExpWeight
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CompExp

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
theorem _root_.solution (hc : 0 < c) {w₁ w₂ : ℤ} {f g : MvPowerSeries σ K} (hf : W c w₁ f) (hg : W c w₂ g) :
    W c (w₁ + w₂) (f * g) := by
  classical
  intro e
  rw [MvPowerSeries.coeff_mul]
  refine norm_sum_le_of_forall_le_of_nonneg (by positivity) fun p hp => ?_
  have hp : p.1 + p.2 = e := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [norm_mul]
  calc ‖MvPowerSeries.coeff p.1 f‖ * ‖MvPowerSeries.coeff p.2 g‖
      ≤ c ^ (w₁ - (p.1.degree : ℤ)) * c ^ (w₂ - (p.2.degree : ℤ)) :=
        mul_le_mul (hf _) (hg _) (norm_nonneg _) (by positivity)
    _ = c ^ (w₁ + w₂ - (e.degree : ℤ)) := by
        rw [← zpow_add₀ hc.ne', ← hp, map_add]; push_cast; ring_nf
end Formalism.ELL.MultiplicativeWeight
