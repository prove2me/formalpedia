-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_discounted_drift_chord_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:12:16.107395+00:00
-- url     : https://prove2.me/submissions/687d1752-5ce8-466a-966d-a5c7d84bb316

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Topology.MetricSpace.Lipschitz
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem solution
    (w : ℝ → ℝ) (L : ℝ≥0) (a b x m d h q t : ℝ)
    (ha : 0 < a) (hd : 0 ≤ d) (hh : 0 < h)
    (hq : 0 ≤ q) (ht : 0 ≤ t)
    (hx : x ∈ Icc a b) (hm : 0 ≤ m)
    (hlow : a - d * h ≤ x - m)
    (hsmall : d * h < min (a / 2) 1)
    (hLip : LipschitzOnWith L w (Icc (a / 2) (b + 1))) :
    ‖Real.exp (-(q * t)) *
      ((w (x + d * h - m) - w (x - m)) / h)‖ ≤ (L : ℝ) * d := by
  have hsmall₁ := (lt_min_iff.mp hsmall).1
  have hsmall₂ := (lt_min_iff.mp hsmall).2
  have hbase : x - m ∈ Icc (a / 2) (b + 1) := by
    constructor <;> linarith [hx.2]
  have htop : x + d * h - m ∈ Icc (a / 2) (b + 1) := by
    constructor <;> linarith [hx.2]
  have hLip' : ‖w (x + d * h - m) - w (x - m)‖ ≤
      (L : ℝ) * ‖x + d * h - m - (x - m)‖ := by
    simpa only [dist_eq_norm] using
      LipschitzOnWith.dist_le_mul hLip (x + d * h - m) htop (x - m) hbase
  have hdiff : x + d * h - m - (x - m) = d * h := by ring
  simp only [hdiff, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hd hh.le)] at hLip'
  have hquot : ‖(w (x + d * h - m) - w (x - m)) / h‖ ≤ (L : ℝ) * d := by
    simp only [norm_div, Real.norm_eq_abs, abs_of_pos hh]
    apply (div_le_iff₀ hh).2
    nlinarith [hLip']
  have hexp : Real.exp (-(q * t)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hq ht))
  calc
    ‖Real.exp (-(q * t)) *
        ((w (x + d * h - m) - w (x - m)) / h)‖ =
        Real.exp (-(q * t)) *
          ‖(w (x + d * h - m) - w (x - m)) / h‖ := by
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    _ ≤ 1 * ‖(w (x + d * h - m) - w (x - m)) / h‖ :=
      mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
    _ ≤ (L : ℝ) * d := by simpa only [one_mul] using hquot
