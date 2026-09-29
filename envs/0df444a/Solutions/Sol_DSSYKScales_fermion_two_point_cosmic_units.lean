-- Prove2me | solution 1 for DSSYKScales.fermion_two_point_cosmic_units
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:45:43.812281+00:00
-- url     : https://prove2.me/submissions/b91793a5-89eb-4f0b-9a54-89d7a4d8ba8f

import Mathlib
import Definitions.Def_DSSYKScales_defs

open Filter Topology

namespace DSSYKScales

theorem aux_f2p_cosh_le (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  have : Real.exp (-|x|) ≤ Real.exp |x| :=
    Real.exp_le_exp.mpr (by linarith [abs_nonneg x])
  linarith

theorem aux_f2p_le_cosh (x : ℝ) : Real.exp |x| / 2 ≤ Real.cosh x := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  have : 0 < Real.exp (-|x|) := Real.exp_pos _
  linarith

theorem aux_f2p_log_cosh_le (x : ℝ) : Real.log (Real.cosh x) ≤ |x| := by
  rw [Real.log_le_iff_le_exp (Real.cosh_pos x)]
  exact aux_f2p_cosh_le x

theorem aux_f2p_le_log_cosh (x : ℝ) : |x| - Real.log 2 ≤ Real.log (Real.cosh x) := by
  have h1 : Real.log (Real.exp |x| / 2) ≤ Real.log (Real.cosh x) :=
    Real.log_le_log (by positivity) (aux_f2p_le_cosh x)
  rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at h1
  exact h1

end DSSYKScales

open DSSYKScales

theorem solution (q : ℕ → ℕ) (J tc : ℝ)
    (hq : Tendsto (fun n => (q n : ℝ)) atTop atTop) :
    Tendsto (fun n => (1 / Real.cosh (J * ((q n : ℝ) * tc)) ^ 2) ^ (1 / (q n : ℝ)))
      atTop (𝓝 (Real.exp (-(2 * |J| * |tc|)))) := by
  have hpos : ∀ᶠ n in atTop, (0:ℝ) < q n := hq.eventually_gt_atTop 0
  set h : ℕ → ℝ := fun n =>
    -(2 * Real.log (Real.cosh (J * ((q n : ℝ) * tc)))) / (q n : ℝ) with hdef
  have habs : ∀ n, |J * ((q n : ℝ) * tc)| = |J| * |tc| * (q n : ℝ) := by
    intro n
    rw [abs_mul, abs_mul, Nat.abs_cast]; ring
  have hh : Tendsto h atTop (𝓝 (-(2 * |J| * |tc|))) := by
    have hinv : Tendsto (fun n => (q n : ℝ)⁻¹) atTop (𝓝 0) := hq.inv_tendsto_atTop
    have hup : Tendsto (fun n => -(2 * |J| * |tc|) + 2 * Real.log 2 * (q n : ℝ)⁻¹) atTop
        (𝓝 (-(2 * |J| * |tc|))) := by
      have := (hinv.const_mul (2 * Real.log 2)).const_add (-(2 * |J| * |tc|))
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hpos] with n hn
      have hb := aux_f2p_log_cosh_le (J * ((q n : ℝ) * tc))
      rw [habs] at hb
      simp only [hdef]
      rw [le_div_iff₀ hn]
      nlinarith
    · filter_upwards [hpos] with n hn
      have hb := aux_f2p_le_log_cosh (J * ((q n : ℝ) * tc))
      rw [habs] at hb
      simp only [hdef]
      rw [div_le_iff₀ hn, add_mul, inv_mul_cancel_right₀ hn.ne']
      nlinarith
  have := (Real.continuous_exp.tendsto _).comp hh
  refine this.congr' ?_
  filter_upwards [hpos] with n hn
  simp only [Function.comp, hdef]
  have hc : 0 < Real.cosh (J * ((q n : ℝ) * tc)) := Real.cosh_pos _
  rw [Real.rpow_def_of_pos (by positivity)]
  congr 1
  rw [one_div, Real.log_inv, Real.log_pow]
  push_cast
  field_simp
