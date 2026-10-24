-- Prove2me | solution 1 for EnergyMomentum.lorentzFactor_eq_sqrt_momentum
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-24T03:25:04.483361+00:00
-- url     : https://prove2.me/submissions/b2265355-8edf-4736-b25e-fd5d015d9e98

import Definitions.Def_EnergyMomentum_basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open EnergyMomentum

theorem solution (m c : ℝ) (v : Vec3)
    (hc : 0 < c) (hm : 0 < m) (hv : ‖v‖ < c) :
    lorentzFactor c v = Real.sqrt (1 + (‖momentum m c v‖ / (m * c)) ^ 2) := by
  have hr0 : 0 ≤ ‖v‖ / c := div_nonneg (norm_nonneg _) hc.le
  have hr1 : ‖v‖ / c < 1 := (div_lt_one hc).mpr hv
  have hpos : 0 < 1 - (‖v‖ / c) ^ 2 := by nlinarith
  have hspos : 0 < Real.sqrt (1 - (‖v‖ / c) ^ 2) := Real.sqrt_pos.2 hpos
  have hgpos : 0 < lorentzFactor c v := one_div_pos.mpr hspos
  have hgsq : lorentzFactor c v ^ 2 * (1 - (‖v‖ / c) ^ 2) = 1 := by
    unfold lorentzFactor
    rw [div_pow, one_pow, Real.sq_sqrt hpos.le]
    exact div_mul_cancel₀ 1 (ne_of_gt hpos)
  have hnorm : ‖momentum m c v‖ = lorentzFactor c v * m * ‖v‖ := by
    simp only [momentum, norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hgpos hm)]
  have hratio : ‖momentum m c v‖ / (m * c) = lorentzFactor c v * (‖v‖ / c) := by
    rw [hnorm]
    field_simp
  have hid : 1 + (‖momentum m c v‖ / (m * c)) ^ 2 = lorentzFactor c v ^ 2 := by
    rw [hratio]
    nlinarith [hgsq]
  rw [hid, Real.sqrt_sq hgpos.le]

#print axioms solution
