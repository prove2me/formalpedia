-- Prove2me | solution 1 for EnergyMomentum.matter_wave_relation
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T02:22:05.666625+00:00
-- url     : https://prove2.me/submissions/731b7de9-13e7-4d52-98dc-7cef86263715

import Definitions.Def_EnergyMomentum_basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
open EnergyMomentum

theorem solution (m c hbar ω : ℝ) (v k : Vec3)
    (hc : 0 < c) (hm : 0 < m) (hv : ‖v‖ < c) (hhbar : 0 < hbar)
    (hE : energy m c v = hbar * ω) (hp : momentum m c v = hbar • k) :
    (ω / c) ^ 2 = ‖k‖ ^ 2 + (m * c / hbar) ^ 2 := by
  have hr0 : 0 ≤ ‖v‖ / c := div_nonneg (norm_nonneg _) hc.le
  have hr1 : ‖v‖ / c < 1 := (div_lt_one hc).mpr hv
  have hpos : 0 < 1 - (‖v‖ / c) ^ 2 := by nlinarith
  have hgsq : lorentzFactor c v ^ 2 * (1 - (‖v‖ / c) ^ 2) = 1 := by
    unfold lorentzFactor
    rw [div_pow, one_pow, Real.sq_sqrt hpos.le]
    exact div_mul_cancel₀ 1 (ne_of_gt hpos)
  have hgpos : 0 < lorentzFactor c v := by
    unfold lorentzFactor
    exact one_div_pos.mpr (Real.sqrt_pos.2 hpos)
  have hnorm : ‖momentum m c v‖ = lorentzFactor c v * m * ‖v‖ := by
    simp only [momentum, norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hgpos hm)]
  have hsingle : (energy m c v) ^ 2 = (‖momentum m c v‖ * c) ^ 2 + (m * c ^ 2) ^ 2 := by
    rw [hnorm, energy]
    have hid : lorentzFactor c v ^ 2 * (c ^ 2 - ‖v‖ ^ 2) = c ^ 2 := by
      field_simp [hc.ne'] at hgsq
      nlinarith only [hgsq]
    linear_combination (m ^ 2 * c ^ 2) * hid
  rw [hp, norm_smul, Real.norm_of_nonneg hhbar.le, hE] at hsingle
  field_simp [hc.ne', hhbar.ne']
  linear_combination hsingle

#print axioms solution


