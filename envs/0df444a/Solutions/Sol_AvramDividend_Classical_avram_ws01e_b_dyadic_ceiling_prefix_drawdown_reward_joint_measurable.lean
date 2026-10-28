-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_dyadic_ceiling_prefix_drawdown_reward_joint_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T17:32:29.99397+00:00
-- url     : https://prove2.me/submissions/def1c880-0194-45cf-a939-0ad548cf6383

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_dyadic_ceiling_pi_endpoint_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (samples : ℕ → ℝ≥0) (β : ℝ) (n : ℕ) :
    Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) =>
      let r : ℝ≥0 :=
        (Nat.ceil ((z.1 : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) / (2 : ℝ≥0) ^ n
      ENNReal.ofReal (Real.exp
        (-β * ((⨆ i : ℕ, if samples i ≤ r then
          ENNReal.ofReal (z.2 (samples i)) else 0).toReal - z.2 r)))) := by
  classical
  let idx : ℝ≥0 × (ℝ≥0 → ℝ) → ℕ :=
    fun z => Nat.ceil ((z.1 : ℝ) * (2 : ℝ) ^ n)
  let round : ℝ≥0 × (ℝ≥0 → ℝ) → ℝ≥0 :=
    fun z => (idx z : ℝ≥0) / (2 : ℝ≥0) ^ n
  have hidx : Measurable idx :=
    ((measurable_coe_nnreal_real.comp measurable_fst).mul_const
      ((2 : ℝ) ^ n)).nat_ceil
  have hround : Measurable round := by
    have hcast : Measurable (fun k : ℕ => (k : ℝ≥0)) := Measurable.of_discrete
    have hcastidx : Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => (idx z : ℝ≥0)) :=
      hcast.comp hidx
    exact hcastidx.div measurable_const
  have hprefix : Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) =>
      ⨆ i : ℕ, if samples i ≤ round z then
        ENNReal.ofReal (z.2 (samples i)) else 0) := by
    apply Measurable.iSup
    intro i
    exact Measurable.ite
      (measurableSet_le measurable_const hround)
      (ENNReal.measurable_ofReal.comp
        ((measurable_pi_apply (samples i)).comp measurable_snd))
      measurable_const
  have hterminal : Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) =>
      z.2 (round z)) := by
    simpa only [round, idx] using
      avram_ws01e_b_dyadic_ceiling_pi_endpoint_measurable n
  change Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) =>
    ENNReal.ofReal (Real.exp
      (-β * ((⨆ i : ℕ, if samples i ≤ round z then
        ENNReal.ofReal (z.2 (samples i)) else 0).toReal - z.2 (round z)))))
  exact (((hprefix.ennreal_toReal.sub hterminal).const_mul (-β)).exp).ennreal_ofReal
