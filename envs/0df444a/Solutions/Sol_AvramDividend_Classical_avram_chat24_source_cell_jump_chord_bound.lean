-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_source_cell_jump_chord_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:41:02.211211+00:00
-- url     : https://prove2.me/submissions/4091f7b2-77a7-4966-b585-19c55eae5539

import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.EMetricSpace.Lipschitz
import Theorems.Thm_avram_chat24_atomic_prefix_interval_core
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem solution
    (f K : ℝ≥0 → ℝ) (v d a b q : ℝ) (B : ℝ≥0)
    (ha : 0 < a) (hq : 0 ≤ q)
    (hf_down : ∀ r : ℝ≥0, 0 < r → f r ≤ Function.leftLim f r)
    (hK : Monotone K)
    (hsum : Summable (fun r : ℝ≥0 =>
      if 0 < r ∧ r ≤ B then Function.leftLim f r - f r else 0))
    (hsource : ∀ t : ℝ≥0, t ≤ B → f t = (t : ℝ) * d -
      ∑' r : ℝ≥0, if 0 < r ∧ r ≤ t then Function.leftLim f r - f r else 0)
    (s t : ℝ≥0) (hst : s ≤ t) (htB : t ≤ B)
    (hs : v + f s - K s ∈ Icc a b) (ht : v + f t - K t ∈ Icc a b)
    (h m : ℝ) (hgap : (t : ℝ) - (s : ℝ) = h)
    (hmdef : m = d * h - (f t - f s))
    (hsmall : d * h < min (a / 2) 1)
    (w : ℝ → ℝ) (L : ℝ≥0)
    (hLip : LipschitzOnWith L w (Icc (a / 2) (b + 1))) :
    ‖Real.exp (-(q * (t : ℝ))) *
      ((w (v + f s - K s - m) - w (v + f s - K s)) / m)‖ ≤ (L : ℝ) := by
  have hmass := avram_chat24_atomic_prefix_interval_core f d B hsum hsource s t hst htB
  have he : (∑' r : ℝ≥0, if s < r ∧ r ≤ t then
      Function.leftLim f r - f r else 0) = m := by
    rw [hmass.2, hgap, hmdef]
    ring
  have hm : 0 ≤ m := by
    rw [← he]
    apply tsum_nonneg
    intro r
    split_ifs with hr
    · exact sub_nonneg.mpr (hf_down r (lt_of_le_of_lt (show (0 : ℝ≥0) ≤ s from zero_le) hr.1))
    · exact le_rfl
  have hbalance : v + f s - K s - m =
      (v + f t - K t) + (K t - K s) - d * h := by
    rw [hmdef]
    ring
  have hlow : a - d * h ≤ v + f s - K s - m := by
    rw [hbalance]
    linarith [ht.1, hK hst]
  have hsmall' := (lt_min_iff.mp hsmall).1
  have hxm : v + f s - K s - m ∈ Icc (a / 2) (b + 1) := by
    constructor <;> linarith [hs.2]
  have hxb : v + f s - K s ∈ Icc (a / 2) (b + 1) := by
    constructor <;> linarith [hs.1, hs.2]
  have hdist := LipschitzOnWith.dist_le_mul hLip
    (v + f s - K s - m) hxm (v + f s - K s) hxb
  rw [Real.dist_eq, Real.dist_eq] at hdist
  have hgap' : v + f s - K s - m - (v + f s - K s) = -m := by ring
  rw [hgap', abs_neg, abs_of_nonneg hm] at hdist
  have hquot : ‖(w (v + f s - K s - m) - w (v + f s - K s)) / m‖ ≤ (L : ℝ) := by
    by_cases hmz : m = 0
    · simp [hmz]
    · have hmp : 0 < m := lt_of_le_of_ne hm (Ne.symm hmz)
      have hmnorm : ‖m‖ = m := by
        rw [Real.norm_eq_abs, abs_of_nonneg hm]
      rw [norm_div, hmnorm, div_le_iff₀ hmp]
      simpa only [Real.norm_eq_abs] using hdist
  have hexp : Real.exp (-(q * (t : ℝ))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hq t.property))
  calc
    ‖Real.exp (-(q * (t : ℝ))) *
        ((w (v + f s - K s - m) - w (v + f s - K s)) / m)‖ =
        Real.exp (-(q * (t : ℝ))) *
          ‖(w (v + f s - K s - m) - w (v + f s - K s)) / m‖ := by
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    _ ≤ 1 * ‖(w (v + f s - K s - m) - w (v + f s - K s)) / m‖ :=
      mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
    _ ≤ (L : ℝ) := by simpa only [one_mul] using hquot
