-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_negative_mark_kernel_uniform_quadratic_min_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:01:23.554553+00:00
-- url     : https://prove2.me/submissions/e56bfef6-76ba-4c2f-8dda-fa954621c124

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.SetSemiring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_positive_band_lipschitz_source
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_tail_global_value_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original compact-reserve negative-jump coefficient is uniformly controlled by the Levy truncation kernel. -/
theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ u ∈ Icc δ K, ∀ z : ℝ, z < 0 →
        (w (u + z) - w u) ^ 2 ≤ M * min 1 (z ^ 2) := by
  have hK0 : 0 ≤ K := le_trans (le_of_lt hδ) hδK
  obtain ⟨A, hA0, hA⟩ :=
    avram_p4_f3_original_negative_tail_global_value_bound
      w hw_cont hw_neg K hK0
  obtain ⟨B, hB⟩ :=
    avram_p4_f3_original_positive_band_lipschitz_source
      w C hw_smooth (δ / 2) K (by linarith) (by linarith) hK
  let r : ℝ := min (δ / 2) 1
  have hr0 : 0 < r := lt_min (by linarith [hδ]) (by norm_num)
  have hrδ : r ≤ δ / 2 := min_le_left _ _
  have hr1 : r ≤ 1 := min_le_right _ _
  let Q : ℝ := max B 0
  have hQ0 : 0 ≤ Q := le_max_right _ _
  have hBQ : B ≤ Q := le_max_left _ _
  let R : ℝ := 2 * A / r
  have hRId : R * r = 2 * A := by
    dsimp [R]
    field_simp [ne_of_gt hr0]
  let M : ℝ := Q ^ 2 + R ^ 2
  have hM0 : 0 ≤ M := add_nonneg (sq_nonneg Q) (sq_nonneg R)
  have hMsmall : Q ^ 2 ≤ M := by
    dsimp [M]
    nlinarith [sq_nonneg R]
  have hMlarge : (2 * A) ^ 2 ≤ M * r ^ 2 := by
    have hR2 : R ^ 2 * r ^ 2 = (2 * A) ^ 2 := by
      calc
        R ^ 2 * r ^ 2 = (R * r) ^ 2 := by ring
        _ = (2 * A) ^ 2 := by rw [hRId]
    dsimp [M]
    nlinarith [mul_nonneg (sq_nonneg Q) (sq_nonneg r)]
  refine ⟨M, hM0, ?_⟩
  intro u hu z hz
  by_cases hzSmall : -r < z
  · have hzLow : -1 < z := by linarith [hr1]
    have hzSq : z ^ 2 ≤ 1 := by
      have h : 0 ≤ (1 + z) * (1 - z) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    have hzMin : min (1 : ℝ) (z ^ 2) = z ^ 2 := min_eq_right hzSq
    have huHalf : u ∈ Icc (δ / 2) K :=
      ⟨by linarith [hu.1], hu.2⟩
    have huvHalf : u + z ∈ Icc (δ / 2) K :=
      ⟨by linarith [hu.1, hrδ], by linarith [hu.2]⟩
    have hRaw : |w (u + z) - w u| ≤ B * |z| := by
      simpa only [show u + z - u = z by ring] using
        hB u huHalf (u + z) huvHalf
    have hCoef : |w (u + z) - w u| ≤ Q * |z| :=
      le_trans hRaw (mul_le_mul_of_nonneg_right hBQ (abs_nonneg z))
    have hQz0 : 0 ≤ Q * |z| := mul_nonneg hQ0 (abs_nonneg z)
    have hProd :
        0 ≤ (Q * |z| - |w (u + z) - w u|) *
          (Q * |z| + |w (u + z) - w u|) :=
      mul_nonneg (sub_nonneg.mpr hCoef)
        (add_nonneg hQz0 (abs_nonneg _))
    have hSq :
        (w (u + z) - w u) ^ 2 ≤ Q ^ 2 * z ^ 2 := by
      nlinarith [sq_abs (w (u + z) - w u), sq_abs z]
    have hFact : Q ^ 2 * z ^ 2 ≤ M * z ^ 2 :=
      mul_le_mul_of_nonneg_right hMsmall (sq_nonneg z)
    simpa only [hzMin] using hSq.trans hFact
  · have hzLarge : z ≤ -r := le_of_not_gt hzSmall
    have hFirst : |w (u + z)| ≤ A :=
      hA (u + z) (by linarith [hu.2])
    have hSecond : |w u| ≤ A := hA u hu.2
    have hDiff : |w (u + z) - w u| ≤ 2 * A := by
      have hh :
          |w (u + z) - w u| ≤ |w (u + z)| + |w u| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (w (u + z)) (0 : ℝ) (w u))
      linarith
    have hProd :
        0 ≤ (2 * A - |w (u + z) - w u|) *
          (2 * A + |w (u + z) - w u|) :=
      mul_nonneg (by linarith)
        (add_nonneg (by linarith) (abs_nonneg _))
    have hSq : (w (u + z) - w u) ^ 2 ≤ (2 * A) ^ 2 := by
      nlinarith [sq_abs (w (u + z) - w u)]
    have hrSq1 : r ^ 2 ≤ 1 := by
      have h : 0 ≤ (1 - r) * (1 + r) :=
        mul_nonneg (by linarith [hr1]) (by linarith [hr0])
      nlinarith
    have hrSqZ : r ^ 2 ≤ z ^ 2 := by
      have h : 0 ≤ (-z - r) * (-z + r) :=
        mul_nonneg (by linarith [hzLarge]) (by linarith [hzLarge, hr0])
      nlinarith
    have hBound : r ^ 2 ≤ min (1 : ℝ) (z ^ 2) :=
      le_min hrSq1 hrSqZ
    have hMstep : M * r ^ 2 ≤ M * min 1 (z ^ 2) :=
      mul_le_mul_of_nonneg_left hBound hM0
    exact hSq.trans (hMlarge.trans hMstep)
