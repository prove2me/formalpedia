-- Prove2me | solution 1 for EnergyMomentum.energy_momentum_relation
-- status  : ACCEPTED   (prove)
-- author  : @Yivy Yu
-- created : 2026-10-23T00:59:58.642163+00:00
-- url     : https://prove2.me/submissions/8d7d4040-886b-437c-83f4-48315fc16dc3

import Mathlib
import Definitions.Def_EnergyMomentum_basic

open EnergyMomentum

theorem solution (m c : ℝ) (v : Vec3)
    (hc : 0 < c) (hm : 0 < m) (hv : ‖v‖ < c) :
    energy m c v ^ 2 = (‖momentum m c v‖ * c) ^ 2 + (m * c ^ 2) ^ 2 := by
  let β : ℝ := ‖v‖ / c
  let s : ℝ := Real.sqrt (1 - β ^ 2)
  let γ : ℝ := 1 / s
  have hβnonneg : 0 ≤ β := div_nonneg (norm_nonneg v) hc.le
  have hβlt : β < 1 := (div_lt_one hc).2 hv
  have hβabs : |β| < 1 := by
    rw [abs_of_nonneg hβnonneg]
    exact hβlt
  have hβsq : β ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one β).2 hβabs
  have hd : 0 < 1 - β ^ 2 := sub_pos.mpr hβsq
  have hsqrt : s ^ 2 = 1 - β ^ 2 := Real.sq_sqrt hd.le
  have hsqrt0 : s ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hd)
  have hγpos : 0 < γ := by
    exact one_div_pos.mpr (Real.sqrt_pos.2 hd)
  have hfactor : γ ^ 2 * (1 - β ^ 2) = 1 := by
    rw [← hsqrt]
    dsimp [γ]
    field_simp
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hpoly : γ ^ 2 * (c ^ 2 - ‖v‖ ^ 2) = c ^ 2 := by
    dsimp [β] at hfactor
    field_simp [hc0] at hfactor
    exact hfactor
  have hγdef : lorentzFactor c v = γ := by
    rfl
  have hscalar : 0 < lorentzFactor c v * m := mul_pos (hγdef.symm ▸ hγpos) hm
  have hnorm : ‖momentum m c v‖ = (lorentzFactor c v * m) * ‖v‖ := by
    rw [momentum, norm_smul, Real.norm_eq_abs, abs_of_pos hscalar]
  rw [hnorm]
  simp only [energy, hγdef]
  have hscaled := congrArg (fun z : ℝ => z * (m * c) ^ 2) hpoly
  ring_nf at hscaled ⊢
  linarith
