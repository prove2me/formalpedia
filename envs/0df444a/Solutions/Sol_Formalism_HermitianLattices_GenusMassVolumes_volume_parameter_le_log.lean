-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.volume_parameter_le_log
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:54:50.121239+00:00
-- url     : https://prove2.me/submissions/78fe7ddd-0662-4b1e-80e5-7275ae26a19f

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FactorialProductRearrangement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset
open Formalism.LogVandermondeBounds.StandardLattice
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : LogVolumeLeParameter := by
  intro ε C₀ A hε hC hA
  have hε0 := hε.ne'
  set K := Real.log 2 + 5 * C₀ / ε + A / 2 + 25 * A / (2 * ε ^ 2) with hK
  have hK0 : 0 ≤ K := by
    have a1 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    have a2 : 0 ≤ 5 * C₀ / ε := by positivity
    have a3 : 0 ≤ A / 2 := by positivity
    have a4 : 0 ≤ 25 * A / (2 * ε ^ 2) := by positivity
    rw [hK]
    linarith
  refine ⟨max 1 ((K + 1) ^ (5 / ε)), ?_⟩
  intro x hx n q d hn hq hd hnx hqx hdx
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : 0 < x := by linarith
  have hy1 : K + 1 ≤ x ^ (ε / 5) := by
    have h1 : (K + 1) ^ (5 / ε) ≤ x := le_trans (le_max_right _ _) hx
    have h2 : ((K + 1) ^ (5 / ε)) ^ (ε / 5) ≤ x ^ (ε / 5) :=
      Real.rpow_le_rpow (by positivity) h1 (by positivity)
    have h3 : (5 / ε) * (ε / 5) = 1 := by
      first | (field_simp; done) | (field_simp; ring)
    rwa [← Real.rpow_mul (by positivity), h3, Real.rpow_one] at h2
  have hxe : x ^ ε = (x ^ (ε / 5)) ^ 5 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 1
    push_cast
    ring
  have hlogx : Real.log x ≤ 5 / ε * x ^ (ε / 5) := by
    have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 (ε / 5))
    rw [Real.log_rpow hx0] at h1
    have h2 : ε / 5 * Real.log x ≤ x ^ (ε / 5) := by linarith
    have h3 : Real.log x = 5 / ε * (ε / 5 * Real.log x) := by
      first | (field_simp; done) | (field_simp; ring)
    rw [h3]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hn0 : 0 < n := by linarith
  have hq0 : 0 < q := by linarith
  have hd0 : 0 < d := by linarith
  have h2n : Real.log (2 * n) ≤ Real.log 2 + C₀ * Real.log x := by
    rw [Real.log_mul (by norm_num) hn0.ne']
    have h := Real.log_le_log hn0 hnx
    rw [Real.log_rpow hx0] at h
    linarith
  have hqd : Real.log (q * d) = Real.log q + Real.log d := Real.log_mul hq0.ne' hd0.ne'
  have hy0 : 1 ≤ x ^ (ε / 5) := by linarith
  have hy3 : x ^ (ε / 5) ≤ (x ^ (ε / 5)) ^ 3 := by
    first | exact le_self_pow₀ hy0 (by norm_num) | exact le_self_pow hy0 (by norm_num)
  have hy2 : x ^ (ε / 5) ≤ (x ^ (ε / 5)) ^ 2 := by
    first | exact le_self_pow₀ hy0 (by norm_num) | exact le_self_pow hy0 (by norm_num)
  have hy3' : 1 ≤ (x ^ (ε / 5)) ^ 3 := le_trans hy0 hy3
  have hsq : (Real.log x) ^ 2 ≤ (5 / ε * x ^ (ε / 5)) ^ 2 := pow_le_pow_left₀ hlog0 hlogx 2
  have t1 : C₀ * Real.log x ≤ 5 * C₀ / ε * x ^ (ε / 5) := by
    have h := mul_le_mul_of_nonneg_left hlogx hC
    calc C₀ * Real.log x ≤ C₀ * (5 / ε * x ^ (ε / 5)) := h
      _ = 5 * C₀ / ε * x ^ (ε / 5) := by ring
  have t2 : A * x ^ (ε / 5) * (Real.log x) ^ 2 ≤ 25 * A / ε ^ 2 * (x ^ (ε / 5)) ^ 3 := by
    have hAy : 0 ≤ A * x ^ (ε / 5) := by positivity
    calc A * x ^ (ε / 5) * (Real.log x) ^ 2 ≤ A * x ^ (ε / 5) * (5 / ε * x ^ (ε / 5)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq hAy
      _ = 25 * A / ε ^ 2 * (x ^ (ε / 5)) ^ 3 := by
          first | (field_simp; done) | (field_simp; ring)
  have c1 : 5 * C₀ / ε * x ^ (ε / 5) ≤ 5 * C₀ / ε * (x ^ (ε / 5)) ^ 3 :=
    mul_le_mul_of_nonneg_left hy3 (by positivity)
  have c2 : A * x ^ (ε / 5) ≤ A * (x ^ (ε / 5)) ^ 3 := mul_le_mul_of_nonneg_left hy3 hA
  have c3 : Real.log 2 ≤ Real.log 2 * (x ^ (ε / 5)) ^ 3 :=
    le_mul_of_one_le_right (Real.log_nonneg (by norm_num)) hy3'
  have main : Real.log (2 * n) + Real.log (q * d) / 2 ≤ K * (x ^ (ε / 5)) ^ 3 := by
    rw [hqd, hK]
    have e : (Real.log 2 + 5 * C₀ / ε + A / 2 + 25 * A / (2 * ε ^ 2)) * (x ^ (ε / 5)) ^ 3 =
        Real.log 2 * (x ^ (ε / 5)) ^ 3 + 5 * C₀ / ε * (x ^ (ε / 5)) ^ 3 +
          (A * (x ^ (ε / 5)) ^ 3) / 2 + (25 * A / ε ^ 2 * (x ^ (ε / 5)) ^ 3) / 2 := by
      first | (field_simp; done) | (field_simp; ring) | ring
    rw [e]
    linarith
  have hKy : K ≤ (x ^ (ε / 5)) ^ 2 := by linarith
  rw [hxe]
  calc Real.log (2 * n) + Real.log (q * d) / 2 ≤ K * (x ^ (ε / 5)) ^ 3 := main
    _ ≤ (x ^ (ε / 5)) ^ 2 * (x ^ (ε / 5)) ^ 3 :=
        mul_le_mul_of_nonneg_right hKy (by positivity)
    _ = (x ^ (ε / 5)) ^ 5 := by ring
end Formalism.HermitianLattices.GenusMassVolumes
