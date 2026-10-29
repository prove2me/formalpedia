-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_true_drawdown_limsup_test_joint_measurable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:08:57.744029+00:00
-- url     : https://prove2.me/submissions/8ed5d3d0-c3b5-4b18-8696-0a1814c9262d

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (samples : ℕ → ℝ≥0) (β : ℝ) :
    Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) =>
      ⨅ k : ℕ, ⨆ n : ℕ, if k ≤ n then
        let r : ℝ≥0 :=
          (Nat.ceil ((z.1 : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) / (2 : ℝ≥0) ^ n
        ENNReal.ofReal (Real.exp
          (-β * ((⨆ i : ℕ, if samples i ≤ r then
            ENNReal.ofReal (z.2 (samples i)) else 0).toReal - z.2 r)))
      else 0) := by
  refine Measurable.iInf fun k => Measurable.iSup fun n => ?_
  by_cases hkn : k ≤ n
  · simp only [hkn, if_true]
    let h : (ℝ≥0 → ℝ) × ℕ → ℝ≥0∞ := fun w =>
      ENNReal.ofReal (Real.exp
          (-β * ((⨆ i : ℕ, if samples i ≤ ((w.2 : ℝ≥0) / (2 : ℝ≥0) ^ n) then
            ENNReal.ofReal (w.1 (samples i)) else 0).toReal - w.1 ((w.2 : ℝ≥0) / (2 : ℝ≥0) ^ n))))
    have hh : Measurable h := by
      refine measurable_from_prod_countable_left fun m => ?_
      refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        (measurable_const.mul (Measurable.sub (Measurable.ennreal_toReal
          (Measurable.iSup fun i => ?_)) (measurable_pi_apply (((m : ℝ≥0)) / (2 : ℝ≥0) ^ n)))))
      dsimp only
      split_ifs
      · exact ENNReal.measurable_ofReal.comp (measurable_pi_apply _)
      · exact measurable_const
    have hg : Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) =>
        (z.2, Nat.ceil ((z.1 : ℝ) * (2 : ℝ) ^ n))) :=
by
      have h1 : Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => ((z.1 : ℝ) * (2 : ℝ) ^ n)) := by fun_prop
      have h2 : Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => Nat.ceil ((z.1 : ℝ) * (2 : ℝ) ^ n)) :=
        (Nat.measurable_ceil (R := ℝ)).comp h1
      exact measurable_snd.prodMk h2
    have := hh.comp hg
    convert this using 1
    funext z
    simp only [h, Function.comp_apply]
  · simp only [hkn, if_false]
    exact measurable_const
