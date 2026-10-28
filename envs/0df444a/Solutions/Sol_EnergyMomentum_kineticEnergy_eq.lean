-- Prove2me | solution 1 for EnergyMomentum.kineticEnergy_eq
-- status  : ACCEPTED   (prove)
-- author  : @Yivy Yu
-- created : 2026-10-26T00:59:45.38029+00:00
-- url     : https://prove2.me/submissions/9210d402-bbbd-478c-ad96-3650e0810647

import Mathlib
import Definitions.Def_EnergyMomentum_basic
import Theorems.Thm_EnergyMomentum_energy_momentum_relation

open EnergyMomentum

theorem solution (m c : ℝ) (v : Vec3)
    (hc : 0 < c) (hm : 0 < m) (hv : ‖v‖ < c) :
    kineticEnergy m c v
      = Real.sqrt ((‖momentum m c v‖ * c) ^ 2 + (m * c ^ 2) ^ 2) - m * c ^ 2 := by
  have hratio_nonneg : 0 ≤ ‖v‖ / c := div_nonneg (norm_nonneg v) hc.le
  have hratio_lt : ‖v‖ / c < 1 := (div_lt_one hc).2 hv
  have hratio_abs : |‖v‖ / c| < 1 := by
    rw [abs_of_nonneg hratio_nonneg]
    exact hratio_lt
  have hratio_sq : (‖v‖ / c) ^ 2 < 1 :=
    (sq_lt_one_iff_abs_lt_one (‖v‖ / c)).2 hratio_abs
  have hden : 0 < 1 - (‖v‖ / c) ^ 2 := sub_pos.mpr hratio_sq
  have hgamma : 0 < lorentzFactor c v := by
    exact one_div_pos.mpr (Real.sqrt_pos.2 hden)
  have henergy : 0 < energy m c v := by
    exact mul_pos (mul_pos hgamma hm) (sq_pos_of_pos hc)
  have hrelation := energy_momentum_relation m c v hc hm hv
  have hsqrt :
      Real.sqrt ((‖momentum m c v‖ * c) ^ 2 + (m * c ^ 2) ^ 2) =
        energy m c v := by
    rw [← hrelation, Real.sqrt_sq_eq_abs, abs_of_pos henergy]
  rw [kineticEnergy, restEnergy, hsqrt]
