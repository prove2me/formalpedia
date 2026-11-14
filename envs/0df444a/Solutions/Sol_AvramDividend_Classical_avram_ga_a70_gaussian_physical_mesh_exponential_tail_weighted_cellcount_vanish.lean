-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a70_gaussian_physical_mesh_exponential_tail_weighted_cellcount_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:57:08.521207+00:00
-- url     : https://prove2.me/submissions/d70444d5-b1e7-4e9b-a204-45ea9c8deb95

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Topology.Neighborhoods
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology AvramDividend.Classical

/-- The total expected positive Gaussian rare-cell error vanishes despite a linearly increasing physical mesh cell count. -/
theorem solution (b c : ℝ) (hc : 0 < c) :
    Tendsto (fun m : ℕ =>
      (((m : ℝ) + 1) * Real.exp (b - c * ((m : ℝ) + 1))))
      atTop (𝓝 (0 : ℝ)) := by
  have hn : Tendsto (fun m : ℕ => (m : ℝ) + 1) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto
      (fun m : ℕ => (m : ℝ)) atTop atTop).atTop_add tendsto_const_nhds
  have hu : Tendsto (fun m : ℕ => c * ((m : ℝ) + 1)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc hn
  have hg : Tendsto (fun m : ℕ =>
      (c * ((m : ℝ) + 1)) ^ 1 *
        Real.exp (-(c * ((m : ℝ) + 1))))
      atTop (𝓝 (0 : ℝ)) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hu
  have hscaled : Tendsto (fun m : ℕ =>
      (Real.exp b / c) * ((c * ((m : ℝ) + 1)) ^ 1 *
        Real.exp (-(c * ((m : ℝ) + 1)))))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hg.const_mul (Real.exp b / c)
  convert hscaled using 1
  funext m
  simp only [pow_one]
  calc
    ((m : ℝ) + 1) * Real.exp (b - c * ((m : ℝ) + 1)) =
      ((m : ℝ) + 1) * (Real.exp b *
        Real.exp (-(c * ((m : ℝ) + 1)))) := by
          rw [sub_eq_add_neg, Real.exp_add]
    _ = (Real.exp b / c) * (c * ((m : ℝ) + 1) *
      Real.exp (-(c * ((m : ℝ) + 1)))) := by
        field_simp [ne_of_gt hc] <;> ring
