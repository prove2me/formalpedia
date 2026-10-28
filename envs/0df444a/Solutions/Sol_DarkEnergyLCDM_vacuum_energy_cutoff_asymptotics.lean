-- Prove2me | solution 1 for DarkEnergyLCDM.vacuum_energy_cutoff_asymptotics
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:34:07.881334+00:00
-- url     : https://prove2.me/submissions/38a5de01-e785-4e44-9f7c-59cb3d00f266

import Mathlib
import Definitions.Def_DarkEnergyLCDM_Defs

open Real Filter Topology MeasureTheory
open DarkEnergyLCDM

namespace LUVac

theorem radial (m K : ℝ) (hK : 0 < K) :
    vacuumEnergyCutoff m K = (∫ y in (0:ℝ)..K, y ^ 2 * Real.sqrt (y ^ 2 + m ^ 2)) / (4 * π ^ 2) := by
  unfold vacuumEnergyCutoff
  set g : ℝ → ℝ := fun r => (1 / 2) * Real.sqrt (r ^ 2 + m ^ 2) / (2 * π) ^ 3 with hg
  have h1 : (∫ k in Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) K,
      (1 / 2) * Real.sqrt (‖k‖ ^ 2 + m ^ 2) / (2 * π) ^ 3)
      = ∫ k : EuclideanSpace ℝ (Fin 3), (Set.Iic K).indicator g ‖k‖ := by
    rw [← integral_indicator Metric.isClosed_closedBall.measurableSet]
    congr 1; funext k
    simp only [Set.indicator, Metric.mem_closedBall, dist_zero_right, Set.mem_Iic, hg]
  rw [h1, integral_fun_norm_addHaar volume ((Set.Iic K).indicator g)]
  have h2 : (∫ (y : ℝ) in Set.Ioi 0,
      y ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1) • (Set.Iic K).indicator g y)
      = ∫ y in (0:ℝ)..K, y ^ 2 * g y := by
    rw [intervalIntegral.integral_of_le hK.le, ← Set.Ioi_inter_Iic,
      ← setIntegral_indicator measurableSet_Iic]
    congr 1; funext y
    simp only [finrank_euclideanSpace_fin, smul_eq_mul, Set.indicator]
    split_ifs <;> simp
  rw [h2]
  simp only [finrank_euclideanSpace_fin, Measure.real, EuclideanSpace.volume_ball_fin_three, hg]
  have h3 : (∫ (y : ℝ) in 0..K, y ^ 2 * (1 / 2 * √(y ^ 2 + m ^ 2) / (2 * π) ^ 3))
      = (1 / 2 / (2 * π) ^ 3) * ∫ (y : ℝ) in 0..K, y ^ 2 * √(y ^ 2 + m ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext y; ring
  rw [h3, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by norm_num),
    ENNReal.toReal_ofReal (by positivity), nsmul_eq_mul]
  simp only [smul_eq_mul]
  push_cast
  have := Real.pi_pos.ne'
  field_simp
  ring

end LUVac

theorem solution (m : ℝ) :
    Tendsto (fun klim : ℝ => vacuumEnergyCutoff m klim / (klim ^ 4 / (16 * π ^ 2)))
      atTop (𝓝 1) := by
  have hb : ∀ K : ℝ, 0 < K →
      1 ≤ vacuumEnergyCutoff m K / (K ^ 4 / (16 * π ^ 2)) ∧
      vacuumEnergyCutoff m K / (K ^ 4 / (16 * π ^ 2)) ≤ 1 + (4 * |m| / 3) * K⁻¹ := by
    intro K hK
    rw [LUVac.radial m K hK]
    set Φ := ∫ y in (0:ℝ)..K, y ^ 2 * Real.sqrt (y ^ 2 + m ^ 2) with hΦ
    have hc : Continuous (fun y : ℝ => y ^ 2 * Real.sqrt (y ^ 2 + m ^ 2)) := by fun_prop
    have hlo : K ^ 4 / 4 ≤ Φ := by
      have : ∫ y in (0:ℝ)..K, y ^ 3 ≤ Φ := by
        apply intervalIntegral.integral_mono_on hK.le
        · exact (continuous_pow 3).intervalIntegrable _ _
        · exact hc.intervalIntegrable _ _
        · intro y hy
          have hy0 : 0 ≤ y := hy.1
          have hs := Real.sq_sqrt (by positivity : 0 ≤ y ^ 2 + m ^ 2)
          have hs0 := Real.sqrt_nonneg (y ^ 2 + m ^ 2)
          have : y ≤ Real.sqrt (y ^ 2 + m ^ 2) := by nlinarith [sq_nonneg m]
          have := mul_le_mul_of_nonneg_left this (sq_nonneg y)
          nlinarith
      simp [integral_pow] at this; norm_num at this; linarith
    have hhi : Φ ≤ K ^ 4 / 4 + |m| * (K ^ 3 / 3) := by
      have : Φ ≤ ∫ y in (0:ℝ)..K, (y ^ 3 + |m| * y ^ 2) := by
        apply intervalIntegral.integral_mono_on hK.le
        · exact hc.intervalIntegrable _ _
        · exact (by fun_prop : Continuous (fun y : ℝ => y ^ 3 + |m| * y ^ 2)).intervalIntegrable _ _
        · intro y hy
          have hy0 : 0 ≤ y := hy.1
          have hs := Real.sq_sqrt (by positivity : 0 ≤ y ^ 2 + m ^ 2)
          have hs0 := Real.sqrt_nonneg (y ^ 2 + m ^ 2)
          have hm2 : m ^ 2 = |m| ^ 2 := (sq_abs m).symm
          have hma := abs_nonneg m
          have : Real.sqrt (y ^ 2 + m ^ 2) ≤ y + |m| := by nlinarith
          have := mul_le_mul_of_nonneg_left this (sq_nonneg y)
          nlinarith
      rw [intervalIntegral.integral_add ((continuous_pow 3).intervalIntegrable _ _)
        ((by fun_prop : Continuous (fun y : ℝ => |m| * y ^ 2)).intervalIntegrable _ _),
        intervalIntegral.integral_const_mul] at this
      simp [integral_pow] at this; norm_num at this; linarith
    have hpi := Real.pi_pos
    have hK4 : 0 < K ^ 4 := by positivity
    have e : Φ / (4 * π ^ 2) / (K ^ 4 / (16 * π ^ 2)) = 4 * Φ / K ^ 4 := by
      field_simp; ring
    rw [e]
    constructor
    · rw [le_div_iff₀ hK4]; linarith
    · rw [div_le_iff₀ hK4]
      have : (1 + 4 * |m| / 3 * K⁻¹) * K ^ 4 = K ^ 4 + 4 * |m| / 3 * K ^ 3 := by
        field_simp
      rw [this]; linarith
  have hup : Tendsto (fun K : ℝ => 1 + (4 * |m| / 3) * K⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_inv_atTop_zero.const_mul (4 * |m| / 3)).const_add (1:ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with K hK using (hb K hK).1
  · filter_upwards [eventually_gt_atTop 0] with K hK using (hb K hK).2
