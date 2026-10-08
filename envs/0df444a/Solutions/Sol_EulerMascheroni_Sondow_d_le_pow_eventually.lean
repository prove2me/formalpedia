-- Prove2me | solution 1 for EulerMascheroni.Sondow.d_le_pow_eventually
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-04T23:56:49.269604+00:00
-- url     : https://prove2.me/submissions/2f8a1939-e282-4e36-beec-49267a75163d

import Theorems.Thm_ZetaNine_HarmonicStability_psi_pnt_rate
import Definitions.Def_eulerMascheroni_sondow
import Mathlib.NumberTheory.Chebyshev

open Filter Topology EulerMascheroni.Sondow

theorem solution (b : ℝ) (hb : Real.exp 1 < b) :
    ∀ᶠ m : ℕ in Filter.atTop, (d m : ℝ) ≤ b ^ m := by
  have hb0 : 0 < b := lt_trans (Real.exp_pos 1) hb
  have hlog : 1 < Real.log b := by
    rw [← Real.log_exp 1]; exact Real.log_lt_log (Real.exp_pos 1) hb
  have hev : ∀ᶠ x : ℝ in atTop, Chebyshev.psi x / x < Real.log b :=
    ZetaNine.HarmonicStability.psi_pnt_rate.eventually (Iio_mem_nhds hlog)
  have hev' := tendsto_natCast_atTop_atTop.eventually hev
  filter_upwards [hev', eventually_gt_atTop 0] with m hm hm0
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm0
  have hpsi : Chebyshev.psi m ≤ m * Real.log b := by
    have := (div_lt_iff₀ hmpos).mp hm
    linarith
  have hd : (d m : ℝ) = (Nat.lcmUpto m : ℝ) := rfl
  have hdpos : (0 : ℝ) < (d m : ℝ) := by
    rw [hd]; exact_mod_cast Nat.lcmUpto_pos m
  rw [Chebyshev.psi_eq_log_lcmUpto, ← hd] at hpsi
  calc (d m : ℝ) = Real.exp (Real.log (d m)) := (Real.exp_log hdpos).symm
    _ ≤ Real.exp (m * Real.log b) := Real.exp_le_exp.mpr hpsi
    _ = b ^ m := by rw [Real.exp_nat_mul, Real.exp_log hb0]
