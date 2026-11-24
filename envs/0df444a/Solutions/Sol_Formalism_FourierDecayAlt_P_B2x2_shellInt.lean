-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x2.shellInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:01:25.170886+00:00
-- url     : https://prove2.me/submissions/493f6dea-8cb3-400c-aff6-4f89726d561d

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x2
namespace Formalism.FourierDecayAlt.P.B2x2
theorem _root_.solution : ShellInt := by
  intro X _ μ N C d A hN h1 hd hC hdA
  have hSm : ∀ m : ℕ, MeasurableSet {x | N x ≤ (2:ℝ) ^ m} := fun m =>
    measurableSet_le hN measurable_const
  have key : ∀ m : ℕ, ((2:ℝ) ^ m / 2) ^ (-A) * ((2:ℝ) ^ m) ^ d = 2 ^ A * ((2:ℝ) ^ (d - A)) ^ m := by
    intro m
    have e1 : (2:ℝ) ^ m / 2 = (2:ℝ) ^ ((m:ℝ) - 1) := by
      rw [Real.rpow_sub_one (by norm_num : (2:ℝ) ≠ 0), Real.rpow_natCast]
    have e2 : ((2:ℝ) ^ (d - A)) ^ m = (2:ℝ) ^ ((d - A) * m) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    rw [e1, e2, ← Real.rpow_natCast (2:ℝ) m, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), ← Real.rpow_add (by norm_num : (0:ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
    ring
  have hpt : ∀ᵐ x ∂μ, ENNReal.ofReal (N x ^ (-A)) ≤
      ∑' m : ℕ, {x | N x ≤ (2:ℝ) ^ m}.indicator (fun _ => ENNReal.ofReal (((2:ℝ) ^ m / 2) ^ (-A))) x := by
    filter_upwards [h1] with x hx
    classical
    have hex : ∃ n : ℕ, N x ≤ (2:ℝ) ^ n := by
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (N x) (by norm_num : (1:ℝ) < 2)
      exact ⟨n, hn.le⟩
    let m0 := Nat.find hex
    have hm0 : N x ≤ (2:ℝ) ^ m0 := Nat.find_spec hex
    have hlow : (2:ℝ) ^ m0 / 2 ≤ N x := by
      rcases Nat.eq_zero_or_pos m0 with h0 | h0
      · rw [h0]
        norm_num
        linarith
      · obtain ⟨n, hn⟩ : ∃ n, m0 = n + 1 := ⟨m0 - 1, by omega⟩
        have hmin := Nat.find_min hex (show n < m0 by omega)
        push_neg at hmin
        rw [hn, pow_succ]
        linarith
    calc ENNReal.ofReal (N x ^ (-A)) ≤ ENNReal.ofReal (((2:ℝ) ^ m0 / 2) ^ (-A)) :=
          by
            apply ENNReal.ofReal_le_ofReal
            rw [Real.rpow_neg (by linarith), Real.rpow_neg (by positivity), inv_eq_one_div,
              inv_eq_one_div]
            exact one_div_le_one_div_of_le (by positivity)
              (Real.rpow_le_rpow (by positivity) hlow (by linarith))
      _ = {x | N x ≤ (2:ℝ) ^ m0}.indicator (fun _ => ENNReal.ofReal (((2:ℝ) ^ m0 / 2) ^ (-A))) x := by
          rw [Set.indicator_of_mem (show x ∈ {x | N x ≤ (2:ℝ) ^ m0} from hm0)]
      _ ≤ ∑' m : ℕ, {x | N x ≤ (2:ℝ) ^ m}.indicator
            (fun _ => ENNReal.ofReal (((2:ℝ) ^ m / 2) ^ (-A))) x := ENNReal.le_tsum m0
  have hq0 : 0 ≤ (2:ℝ) ^ (d - A) := by positivity
  have hq1 : (2:ℝ) ^ (d - A) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hsum : Summable fun m : ℕ => |C| * 2 ^ A * ((2:ℝ) ^ (d - A)) ^ m :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  calc ∫⁻ x, ENNReal.ofReal (N x ^ (-A)) ∂μ
      ≤ ∫⁻ x, ∑' m : ℕ, {x | N x ≤ (2:ℝ) ^ m}.indicator
          (fun _ => ENNReal.ofReal (((2:ℝ) ^ m / 2) ^ (-A))) x ∂μ := lintegral_mono_ae hpt
    _ = ∑' m : ℕ, ENNReal.ofReal (((2:ℝ) ^ m / 2) ^ (-A)) * μ {x | N x ≤ (2:ℝ) ^ m} := by
        rw [lintegral_tsum fun m => (measurable_const.indicator (hSm m)).aemeasurable]
        exact tsum_congr fun m => lintegral_indicator_const (hSm m) _
    _ ≤ ∑' m : ℕ, ENNReal.ofReal (|C| * 2 ^ A * ((2:ℝ) ^ (d - A)) ^ m) := by
        refine ENNReal.tsum_le_tsum fun m => ?_
        have hR : (1:ℝ) ≤ (2:ℝ) ^ m := one_le_pow₀ (by norm_num)
        have hp0 : 0 ≤ ((2:ℝ) ^ m / 2) ^ (-A) := by positivity
        calc ENNReal.ofReal (((2:ℝ) ^ m / 2) ^ (-A)) * μ {x | N x ≤ (2:ℝ) ^ m}
            ≤ ENNReal.ofReal (((2:ℝ) ^ m / 2) ^ (-A)) * ENNReal.ofReal (C * ((2:ℝ) ^ m) ^ d) :=
              mul_le_mul_of_nonneg_left (hC _ hR) zero_le
          _ ≤ ENNReal.ofReal (((2:ℝ) ^ m / 2) ^ (-A)) * ENNReal.ofReal (|C| * ((2:ℝ) ^ m) ^ d) :=
              mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal
                (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))) zero_le
          _ = ENNReal.ofReal (|C| * 2 ^ A * ((2:ℝ) ^ (d - A)) ^ m) := by
              rw [← ENNReal.ofReal_mul hp0]
              congr 1
              calc ((2:ℝ) ^ m / 2) ^ (-A) * (|C| * ((2:ℝ) ^ m) ^ d)
                  = |C| * (((2:ℝ) ^ m / 2) ^ (-A) * ((2:ℝ) ^ m) ^ d) := by ring
                _ = |C| * 2 ^ A * ((2:ℝ) ^ (d - A)) ^ m := by rw [key m]; ring
    _ = ENNReal.ofReal (∑' m : ℕ, |C| * 2 ^ A * ((2:ℝ) ^ (d - A)) ^ m) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsum).symm
    _ < ∞ := ENNReal.ofReal_lt_top
end Formalism.FourierDecayAlt.P.B2x2
