-- Prove2me | solution 1 for Formalism.H.PoissonPeriodization.shift_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:07.317507+00:00
-- url     : https://prove2.me/submissions/1faa58e9-96ea-4c1d-be50-812dc208d36b

import Definitions.Def_Formalism_LatticeTheta_LatticeSummableDecay
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_Periodization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Asymptotics Complex Metric
open scoped RealInnerProductSpace
noncomputable section
open Formalism Formalism.H
open Formalism.H.PoissonPeriodization
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
namespace Formalism.H.PoissonPeriodization
theorem _root_.solution {b : ℝ} (hb : 0 ≤ b) {R : ℝ} (hR : 0 ≤ R) (y x : V) (hx : ‖x‖ ≤ R) :
    (1 + ‖y + x‖) ^ (-b) ≤ (1 + R) ^ b * (1 + ‖y‖) ^ (-b) := by
  have h1 : 0 < 1 + ‖y + x‖ := by positivity
  have h2 : 0 < 1 + ‖y‖ := by positivity
  have h3 : 0 < 1 + R := by linarith
  have key : 1 + ‖y‖ ≤ (1 + ‖y + x‖) * (1 + R) := by
    have hyx : ‖y‖ ≤ ‖y + x‖ + ‖x‖ := by
      calc ‖y‖ = ‖(y + x) - x‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖y + x‖ + ‖x‖ := norm_sub_le _ _
    nlinarith [norm_nonneg (y + x)]
  have key' : (1 + ‖y‖) ^ b ≤ ((1 + ‖y + x‖) * (1 + R)) ^ b := Real.rpow_le_rpow h2.le key hb
  rw [Real.mul_rpow h1.le h3.le] at key'
  have hA := Real.rpow_pos_of_pos h1 b
  have hB := Real.rpow_pos_of_pos h2 b
  rw [Real.rpow_neg h1.le, Real.rpow_neg h2.le, le_mul_inv_iff₀ hB, inv_mul_le_iff₀ hA]
  exact key'
end Formalism.H.PoissonPeriodization
