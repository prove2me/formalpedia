-- Prove2me | solution 1 for Erdos77.rpow_tendsto_implies_log_div_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-26T22:49:08.760975+00:00
-- url     : https://prove2.me/submissions/a13d419c-71eb-4328-b10e-2df70ba2ae22

import Mathlib
open Filter Topology

theorem solution (a : Nat → Real) (L : Real)
    (ha : ∀ᶠ k : Nat in Filter.atTop, 1 ≤ a k)
    (hL : Filter.Tendsto (fun k : Nat => (a k) ^ ((1 : Real) / (k : Real))) Filter.atTop (nhds L))
    (hLpos : 0 < L) :
    Exists fun l : Real => Filter.Tendsto (fun k : Nat => Real.log (a k) / (k : Real)) Filter.atTop (nhds l) := by
  have hlog : Filter.Tendsto
      (fun k : Nat => Real.log ((a k) ^ ((1 : Real) / (k : Real))))
      Filter.atTop (nhds (Real.log L)) :=
    (Real.continuousAt_log (ne_of_gt hLpos)).tendsto.comp hL
  refine ⟨Real.log L, ?_⟩
  apply hlog.congr'
  filter_upwards [ha, eventually_ge_atTop 1] with k hk1 hk2
  have hak : 0 < a k := lt_of_lt_of_le zero_lt_one hk1
  have hkpos : 0 < k := by omega
  have hkne : (k : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hkpos)
  rw [Real.log_rpow hak]
  field_simp
