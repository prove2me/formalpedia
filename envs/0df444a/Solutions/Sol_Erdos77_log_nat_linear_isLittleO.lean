-- Prove2me | solution 1 for Erdos77.log_nat_linear_isLittleO
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T16:19:55.772853+00:00
-- url     : https://prove2.me/submissions/7f33b007-e1eb-48cd-9bc8-26a1c981edf1

import Mathlib
open Filter Topology

theorem solution :
  (fun k : Nat => Real.log (2 * (k : Real) + 1)) =o[atTop] (fun k : Nat => (k : Real)) := by
  have h_arg : Tendsto (fun k : Nat => 2 * (k : Real) + 1) atTop atTop := by
    refine tendsto_atTop_mono ?_ tendsto_natCast_atTop_atTop
    intro k
    have hk : 0 <= (k : Real) := Nat.cast_nonneg k
    linarith
  have h_log : (fun k : Nat => Real.log (2 * (k : Real) + 1)) =o[atTop]
      (fun k : Nat => 2 * (k : Real) + 1) := by
    convert (Real.isLittleO_log_id_atTop.comp_tendsto h_arg) using 1 <;> rfl
  have h_bound : (fun k : Nat => 2 * (k : Real) + 1) =O[atTop]
      (fun k : Nat => (k : Real)) := by
    apply Asymptotics.IsBigO.of_bound 3
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk' : (1 : Real) <= (k : Real) := by exact_mod_cast hk
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 <= 2 * (k : Real) + 1)]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 <= (k : Real))]
    nlinarith
  exact h_log.trans_isBigO h_bound