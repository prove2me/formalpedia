-- Prove2me | solution 1 for EnergyMomentum.minkowski_norm_fourMomentum
-- status  : ACCEPTED   (prove)
-- author  : @Yivy Yu
-- created : 2026-10-24T01:06:38.820144+00:00
-- url     : https://prove2.me/submissions/23d8a9ce-56d2-4153-82cf-56b1194b4c1e

import Mathlib
import Definitions.Def_EnergyMomentum_basic

open EnergyMomentum

theorem solution (m c : ℝ) (v : Vec3)
    (hc : 0 < c) (hm : 0 < m) (hv : ‖v‖ < c) :
    minkowskiInner (fourMomentum m c v) (fourMomentum m c v)
        = (energy m c v / c) ^ 2 - ‖momentum m c v‖ ^ 2 ∧
      minkowskiInner (fourMomentum m c v) (fourMomentum m c v) = (m * c) ^ 2 := by
  have hfirst :
      minkowskiInner (fourMomentum m c v) (fourMomentum m c v) =
        (energy m c v / c) ^ 2 - ‖momentum m c v‖ ^ 2 := by
    simp [minkowskiInner, fourMomentum, pow_two]
  refine ⟨hfirst, ?_⟩
  rw [hfirst]
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
  have hγpos : 0 < γ := one_div_pos.mpr (Real.sqrt_pos.2 hd)
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
  have hscalar : 0 < lorentzFactor c v * m :=
    mul_pos (hγdef.symm ▸ hγpos) hm
  have hnorm : ‖momentum m c v‖ = (lorentzFactor c v * m) * ‖v‖ := by
    rw [momentum, norm_smul, Real.norm_eq_abs, abs_of_pos hscalar]
  rw [hnorm]
  simp only [energy, hγdef]
  field_simp [hc0]
  have hscaled := congrArg (fun z : ℝ => z * m ^ 2) hpoly
  ring_nf at hscaled ⊢
  linarith
