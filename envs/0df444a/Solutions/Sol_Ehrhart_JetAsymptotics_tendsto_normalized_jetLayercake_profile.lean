-- Prove2me | solution 1 for Ehrhart.JetAsymptotics.tendsto_normalized_jetLayercake_profile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/716d0bd2-e8db-4074-a349-0087b2e72dae

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JetAsymptotics_tendsto_floor_mul_div_nat
import Theorems.Thm_Ehrhart_JetAsymptotics_tendsto_choose_floor_mul_div_pow

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.JetAsymptotics
open Asymptotics Filter MeasureTheory
open scoped BigOperators Topology
namespace Ehrhart.JetAsymptotics
theorem _root_.solution {n : ℕ}
    (K : CenteredBody n) {t : ℝ} (ht : 0 < t) :
    Tendsto
      (fun k : ℕ =>
        (((Nat.floor (t * (k : ℝ)) : ℕ) : ℝ) *
            (BergmanMonomials.bergmanDimension K k : ℝ) -
          (((n + Nat.floor (t * (k : ℝ))).choose
            (n + 1) : ℕ) : ℝ)) /
          ((k : ℝ) *
            (BergmanMonomials.bergmanDimension K k : ℝ)))
      atTop
      (𝓝 (t - t ^ (n + 1) /
        (((n + 1).factorial : ℝ) *
          normalizedVolume K.carrier))) := by
  have hfloor := tendsto_floor_mul_div_nat ht.le
  have hchoose :
      Tendsto
        (fun k : ℕ =>
          (((n + Nat.floor (t * (k : ℝ))).choose
            (n + 1) : ℕ) : ℝ) / (k : ℝ) ^ (n + 1))
        atTop
        (𝓝 (t ^ (n + 1) / ((n + 1).factorial : ℝ))) := by
    simpa [Nat.add_comm] using
      tendsto_choose_floor_mul_div_pow (n + 1) n ht
  have hdim :=
    BergmanMonomials.bergmanDimension_div_pow_tendsto_volume K
  have hquot := hchoose.div hdim K.volume_pos.ne'
  have htarget :
      Tendsto
        (fun k : ℕ =>
          (Nat.floor (t * (k : ℝ)) : ℝ) / (k : ℝ) -
            ((((n + Nat.floor (t * (k : ℝ))).choose
              (n + 1) : ℕ) : ℝ) / (k : ℝ) ^ (n + 1)) /
              ((BergmanMonomials.bergmanDimension K k : ℝ) /
                (k : ℝ) ^ n))
        atTop
        (𝓝 (t - t ^ (n + 1) /
          (((n + 1).factorial : ℝ) *
            normalizedVolume K.carrier))) := by
    simpa [div_div] using hfloor.sub hquot
  apply htarget.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
  have hkpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk
  have hkne : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hkpos
  have hdne :
      (BergmanMonomials.bergmanDimension K k : ℝ) ≠ 0 := by
    exact_mod_cast
      (BergmanMonomials.bergmanDimension_pos K hkpos).ne'
  rw [pow_succ]
  field_simp
end Ehrhart.JetAsymptotics
