-- Prove2me | solution 1 for AvramDividend.Classical.integrableOn_Iio_zero_of_isBigO_id_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T15:04:39.071196+00:00
-- url     : https://prove2.me/submissions/1fab362b-d026-48f9-adbd-4dfbcf6ed944

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Asymptotics
open scoped NNReal ENNReal Topology

theorem solution
    (ν : Measure ℝ)
    (hνsq : Integrable (fun y : ℝ => min 1 (y ^ 2)) ν)
    (hνabs : IntegrableOn (fun y : ℝ => |y|) (Ioo (-1) 0) ν)
    (F : ℝ → ℝ) (hF : AEStronglyMeasurable F ν)
    (hsmall : F =O[𝓝 0] (fun y : ℝ => y))
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ y : ℝ, y < 0 → ‖F y‖ ≤ B) :
    IntegrableOn F (Iio 0) ν := by
  rw [isBigO_iff'] at hsmall
  obtain ⟨C, hCpos, hCev⟩ := hsmall
  rw [Metric.eventually_nhds_iff] at hCev
  obtain ⟨ε, hεpos, hε⟩ := hCev
  let d : ℝ := min (ε / 2) (1 / 2)
  have hdpos : 0 < d := by
    dsimp [d]
    exact lt_min (by linarith) (by norm_num)
  have hdε : d < ε := by
    exact lt_of_le_of_lt (min_le_left (ε / 2) (1 / 2)) (by linarith)
  have hd1 : d ≤ 1 := by
    exact (min_le_right (ε / 2) (1 / 2)).trans (by norm_num)
  have hd_sq_pos : 0 < d ^ 2 := sq_pos_of_pos hdpos
  have hd_sq_one : d ^ 2 ≤ 1 := by
    have hm : 0 ≤ (1 - d) * (1 + d) :=
      mul_nonneg (sub_nonneg.mpr hd1) (add_nonneg zero_le_one hdpos.le)
    nlinarith
  let D : ℝ := B / d ^ 2
  have hD0 : 0 ≤ D := by
    dsimp [D]
    exact div_nonneg hB hd_sq_pos.le
  let G : ℝ → ℝ := fun y =>
    C * (Ioo (-1 : ℝ) 0).indicator (fun z : ℝ => |z|) y +
      D * min 1 (y ^ 2)
  have habs_ind :
      Integrable ((Ioo (-1 : ℝ) 0).indicator (fun y : ℝ => |y|)) ν := by
    exact (integrable_indicator_iff measurableSet_Ioo).2 hνabs
  have hG : Integrable G ν := by
    dsimp [G]
    exact (habs_ind.const_mul C).add (hνsq.const_mul D)
  have hdom :
      ∀ y : ℝ, y < 0 → ‖F y‖ ≤ G y := by
    intro y hy
    have hweight0 : 0 ≤ min 1 (y ^ 2) := by
      exact le_min zero_le_one (sq_nonneg y)
    by_cases hnear : |y| < d
    · have hdist : dist y 0 < ε := by
        rw [Real.dist_eq]
        simpa using hnear.trans hdε
      have hCy := hε hdist
      have hy_lower : -1 < y := by
        have hyabs1 : |y| < 1 := hnear.trans_le hd1
        exact (abs_lt.mp hyabs1).1
      have hyI : y ∈ Ioo (-1 : ℝ) 0 := ⟨hy_lower, hy⟩
      have hsecond0 : 0 ≤ D * min 1 (y ^ 2) :=
        mul_nonneg hD0 hweight0
      calc
        ‖F y‖ ≤ C * ‖y‖ := hCy
        _ = C * |y| := by rw [Real.norm_eq_abs]
        _ ≤ C * |y| + D * min 1 (y ^ 2) :=
          le_add_of_nonneg_right hsecond0
        _ = G y := by simp [G, hyI]
    · have hdy : d ≤ |y| := le_of_not_gt hnear
      have hm : 0 ≤ (|y| - d) * (|y| + d) :=
        mul_nonneg (sub_nonneg.mpr hdy)
          (add_nonneg (abs_nonneg y) hdpos.le)
      have hd_sq_y : d ^ 2 ≤ y ^ 2 := by
        nlinarith [sq_abs y]
      have hd_weight : d ^ 2 ≤ min 1 (y ^ 2) :=
        le_min hd_sq_one hd_sq_y
      have hBD : B = D * d ^ 2 := by
        dsimp [D]
        field_simp
      have hind0 :
          0 ≤ (Ioo (-1 : ℝ) 0).indicator (fun z : ℝ => |z|) y := by
        by_cases hyI : y ∈ Ioo (-1 : ℝ) 0
        · simp [hyI, abs_nonneg]
        · simp [hyI]
      have hfirst0 :
          0 ≤ C * (Ioo (-1 : ℝ) 0).indicator (fun z : ℝ => |z|) y :=
        mul_nonneg hCpos.le hind0
      calc
        ‖F y‖ ≤ B := hbound y hy
        _ = D * d ^ 2 := hBD
        _ ≤ D * min 1 (y ^ 2) :=
          mul_le_mul_of_nonneg_left hd_weight hD0
        _ ≤ C * (Ioo (-1 : ℝ) 0).indicator (fun z : ℝ => |z|) y +
              D * min 1 (y ^ 2) :=
          le_add_of_nonneg_left hfirst0
        _ = G y := rfl
  change Integrable F (ν.restrict (Iio 0))
  refine hG.restrict.mono' (hF.mono_measure Measure.restrict_le_self) ?_
  filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
  exact hdom y hy
