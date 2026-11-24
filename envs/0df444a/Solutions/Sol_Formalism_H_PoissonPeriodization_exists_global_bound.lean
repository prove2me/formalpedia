-- Prove2me | solution 1 for Formalism.H.PoissonPeriodization.exists_global_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:07.083375+00:00
-- url     : https://prove2.me/submissions/f60d5aa3-3623-4a1d-a73d-df64fc6e23f1

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
theorem _root_.solution {f : V → ℂ} (hf : Continuous f) {b : ℝ} (hb : 0 ≤ b)
    (hO : f =O[cocompact V] (fun v => ‖v‖ ^ (-b))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v, ‖f v‖ ≤ C * (1 + ‖v‖) ^ (-b) := by
  obtain ⟨c, hc⟩ := hO.bound
  first
    | rw [← cobounded_eq_cocompact] at hc
    | rw [← Metric.cobounded_eq_cocompact] at hc
  rw [← comap_norm_atTop, Filter.eventually_comap, Filter.eventually_atTop] at hc
  obtain ⟨r, hr⟩ := hc
  set r' := max r 1 with hr'
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : V) r').exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max (M * (1 + r') ^ b) (|c| * 2 ^ b), by positivity, fun v => ?_⟩
  by_cases hv : ‖v‖ ≤ r'
  · have h1 := hM v (by simpa using hv)
    have hpos : 0 < 1 + ‖v‖ := by positivity
    have hr1 : 0 < 1 + r' := by
      have : 1 ≤ r' := le_max_right _ _
      linarith
    have hone : 1 ≤ (1 + r') ^ b * (1 + ‖v‖) ^ (-b) := by
      rw [Real.rpow_neg hpos.le, ← div_eq_mul_inv, one_le_div (Real.rpow_pos_of_pos hpos b)]
      exact Real.rpow_le_rpow hpos.le (by linarith) hb
    calc ‖f v‖ ≤ M := h1
      _ ≤ M * ((1 + r') ^ b * (1 + ‖v‖) ^ (-b)) :=
          le_mul_of_one_le_right (le_trans (norm_nonneg _) h1) hone
      _ = M * (1 + r') ^ b * (1 + ‖v‖) ^ (-b) := by ring
      _ ≤ max (M * (1 + r') ^ b) (|c| * 2 ^ b) * (1 + ‖v‖) ^ (-b) := by
          gcongr
          exact le_max_left _ _
  · push_neg at hv
    have hv1 : 1 ≤ ‖v‖ := le_trans (le_max_right _ _) hv.le
    have hb' := hr ‖v‖ (le_trans (le_max_left _ _) hv.le) v rfl
    have hvpos : 0 < ‖v‖ := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] at hb'
    have hk : ‖v‖ ^ (-b) ≤ 2 ^ b * (1 + ‖v‖) ^ (-b) := by
      rw [Real.rpow_neg hvpos.le, Real.rpow_neg (by positivity),
        le_mul_inv_iff₀ (Real.rpow_pos_of_pos (by positivity) b),
        inv_mul_le_iff₀ (Real.rpow_pos_of_pos hvpos b),
        ← Real.mul_rpow hvpos.le (by norm_num : (0 : ℝ) ≤ 2)]
      exact Real.rpow_le_rpow (by positivity) (by linarith) hb
    have hnn : 0 ≤ ‖v‖ ^ (-b) := Real.rpow_nonneg (norm_nonneg _) _
    calc ‖f v‖ ≤ c * ‖v‖ ^ (-b) := hb'
      _ ≤ |c| * ‖v‖ ^ (-b) := mul_le_mul_of_nonneg_right (le_abs_self c) hnn
      _ ≤ |c| * (2 ^ b * (1 + ‖v‖) ^ (-b)) := mul_le_mul_of_nonneg_left hk (abs_nonneg c)
      _ = |c| * 2 ^ b * (1 + ‖v‖) ^ (-b) := by ring
      _ ≤ max (M * (1 + r') ^ b) (|c| * 2 ^ b) * (1 + ‖v‖) ^ (-b) := by
          gcongr
          exact le_max_right _ _
end Formalism.H.PoissonPeriodization
