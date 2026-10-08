-- Prove2me | solution 1 for AvramDividend.Classical.integrableOn_Iio_zero_of_isBigO_sq_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T13:44:55.158982+00:00
-- url     : https://prove2.me/submissions/270b6164-0446-4025-b2e8-2c0436fcf3c1

import Mathlib


set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Asymptotics
open scoped NNReal ENNReal Topology

theorem solution
    (ν : Measure ℝ)
    (hν : Integrable (fun y : ℝ => min 1 (y ^ 2)) ν)
    (F : ℝ → ℝ) (hF : AEStronglyMeasurable F ν)
    (hsmall : F =O[𝓝 0] (fun y : ℝ => y ^ 2))
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
  let K : ℝ := max C D
  have hCK : C ≤ K := by
    exact le_max_left C D
  have hDK : D ≤ K := by
    exact le_max_right C D
  have hK0 : 0 ≤ K := hCpos.le.trans hCK
  have hdom :
      ∀ y : ℝ, y < 0 →
        ‖F y‖ ≤ K * min 1 (y ^ 2) := by
    intro y hy
    by_cases hnear : |y| < d
    · have hdist : dist y 0 < ε := by
        rw [Real.dist_eq]
        simpa using hnear.trans hdε
      have hCy := hε hdist
      have hyabs1 : |y| ≤ 1 := (le_of_lt hnear).trans hd1
      have hysq1 : y ^ 2 ≤ 1 := by
        have hm : 0 ≤ (1 - |y|) * (1 + |y|) :=
          mul_nonneg (sub_nonneg.mpr hyabs1)
            (add_nonneg zero_le_one (abs_nonneg y))
        nlinarith [sq_abs y]
      have hmin : min 1 (y ^ 2) = y ^ 2 := min_eq_right hysq1
      have hnormsq : ‖y ^ 2‖ = y ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg y)]
      calc
        ‖F y‖ ≤ C * ‖y ^ 2‖ := hCy
        _ = C * (y ^ 2) := by rw [hnormsq]
        _ ≤ K * (y ^ 2) :=
          mul_le_mul_of_nonneg_right hCK (sq_nonneg y)
        _ = K * min 1 (y ^ 2) := by rw [hmin]
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
      have hweight0 : 0 ≤ min 1 (y ^ 2) :=
        le_min zero_le_one (sq_nonneg y)
      calc
        ‖F y‖ ≤ B := hbound y hy
        _ = D * d ^ 2 := hBD
        _ ≤ D * min 1 (y ^ 2) :=
          mul_le_mul_of_nonneg_left hd_weight hD0
        _ ≤ K * min 1 (y ^ 2) :=
          mul_le_mul_of_nonneg_right hDK hweight0
  have hmajor :
      Integrable (fun y : ℝ => K * min 1 (y ^ 2)) ν :=
    hν.const_mul K
  change Integrable F (ν.restrict (Iio 0))
  refine (hmajor.restrict).mono' (hF.mono_measure Measure.restrict_le_self) ?_
  filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
  exact hdom y hy
