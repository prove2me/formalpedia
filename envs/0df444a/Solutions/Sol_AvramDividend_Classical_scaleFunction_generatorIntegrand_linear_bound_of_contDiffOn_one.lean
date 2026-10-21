-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generatorIntegrand_linear_bound_of_contDiffOn_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T03:28:15.478297+00:00
-- url     : https://prove2.me/submissions/a807fbb7-061c-45c8-9f9e-3ee0191b0c33

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shift_bounds_of_nonpositive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Asymptotics
open scoped NNReal ENNReal
open scoped Topology

open AvramDividend.Classical


theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a x : ℝ)
    (hC1 : ContDiffOn ℝ 1 W (Ioo 0 a))
    (hx : x ∈ Ioo 0 a) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Iio (0 : ℝ),
        |SpectrallyNegativeLevy.generatorIntegrand W x y| ≤
          C * min 1 |y| := by
  have hx0 : 0 < x := hx.1
  have hcontAt : ContDiffAt ℝ 1 W x :=
    hC1.contDiffAt (isOpen_Ioo.mem_nhds hx)
  have hd : HasDerivAt W (deriv W x) x :=
    (hcontAt.differentiableAt (by norm_num)).hasDerivAt
  have hrem0 : (fun y : ℝ => W (x + y) - W x - y • deriv W x)
      =o[𝓝 0] (fun y : ℝ => y) := hasDerivAt_iff_isLittleO_nhds_zero.mp hd
  have hrem : (fun y : ℝ => W (x + y) - W x - deriv W x * y)
      =o[𝓝 0] (fun y : ℝ => y) := by
    apply hrem0.congr_left
    intro y
    simp [smul_eq_mul, mul_comm]
  have hone : Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) :=
    isOpen_Ioo.mem_nhds (by norm_num)
  have heq : (fun y : ℝ => SpectrallyNegativeLevy.generatorIntegrand W x y)
      =ᶠ[𝓝 0] (fun y : ℝ => W (x + y) - W x - deriv W x * y) := by
    filter_upwards [hone] with y hy
    unfold SpectrallyNegativeLevy.generatorIntegrand
    simp [Set.indicator_of_mem hy]
  have hsmall : (fun y : ℝ => SpectrallyNegativeLevy.generatorIntegrand W x y)
      =O[𝓝 (0 : ℝ)] (fun y : ℝ => y) :=
    hrem.isBigO.congr' heq.symm Filter.EventuallyEq.rfl
  -- The big-`O` constant, from `IsBigOWith.bound`.
  obtain ⟨C, hbig⟩ := hsmall.isBigOWith
  obtain ⟨C, hC, hbig⟩ := hbig.exists_nonneg
  have hbig' : ∀ᶠ y : ℝ in 𝓝 (0 : ℝ),
      |SpectrallyNegativeLevy.generatorIntegrand W x y| ≤ C * |y| := by
    filter_upwards [hbig.bound] with y hy
    simpa [Real.norm_eq_abs] using hy
  -- The eventual estimate, realised by an explicit neighbourhood of 0.
  obtain ⟨v, hv, hvs⟩ := hbig'.exists_mem
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hv
  -- The state part is at most `W x`; the compensation at most `|deriv W x| min 1 |y|`.
  have hWx0 : 0 ≤ W x := hW.2.1 x hx0.le
  have hdecomp : ∀ y : ℝ, y < 0 →
      |SpectrallyNegativeLevy.generatorIntegrand W x y| ≤
        W x + |deriv W x| * min 1 |y| := by
    intro y hy
    have hs := scaleFunction_shift_bounds_of_nonpositive
      X q W hW x y hx0.le (le_of_lt hy)
    have hdiff : |W (x + y) - W x| ≤ W x := by
      rw [abs_of_nonpos (sub_nonpos.mpr hs.2)]
      linarith [hs.1]
    have hcomp : |deriv W x * y * (Ioo (-1 : ℝ) 1).indicator
        (fun _ : ℝ => (1 : ℝ)) y| ≤ |deriv W x| * min 1 |y| := by
      by_cases hI : y ∈ Ioo (-1 : ℝ) 1
      · have habs : |y| < 1 := abs_lt.mpr hI
        have hmin : min 1 |y| = |y| := min_eq_right habs.le
        have h1 : |y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y| ≤ |y| := by
          rw [Set.indicator_of_mem hI]; simp [abs_mul]
        rw [mul_assoc, abs_mul, hmin]
        exact mul_le_mul_of_nonneg_left h1 (abs_nonneg (deriv W x))
      · have hz : (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y = 0 :=
          Set.indicator_of_notMem hI (fun _ : ℝ => (1 : ℝ))
        rw [mul_assoc, hz]
        simp only [mul_zero, abs_zero]
        exact mul_nonneg (abs_nonneg (deriv W x)) (le_min (zero_le_one) (abs_nonneg y))
    calc
      |SpectrallyNegativeLevy.generatorIntegrand W x y|
          ≤ |W (x + y) - W x| +
              |deriv W x * y * (Ioo (-1 : ℝ) 1).indicator
                (fun _ : ℝ => (1 : ℝ)) y| := by
            unfold SpectrallyNegativeLevy.generatorIntegrand
            exact abs_sub _ _
      _ ≤ W x + |deriv W x| * min 1 |y| := add_le_add hdiff hcomp
  have hdiv0 : 0 ≤ W x / δ := div_nonneg hWx0 (le_of_lt hδ)
  let K : ℝ := max (max C (W x / δ + |deriv W x|)) (W x + |deriv W x|)
  have hK : 0 ≤ K := le_max_of_le_left (le_max_of_le_left hC)
  refine ⟨K, hK, ?_⟩
  intro y hy
  have hyneg : y < 0 := (Set.mem_Iio.mp hy)
  by_cases hsmall_y : |y| ≤ 1
  · have hmin : min 1 |y| = |y| := min_eq_right hsmall_y
    by_cases hyδ : δ ≤ |y|
    · have hb2 := hdecomp y hyneg
      have hWeq : W x / δ * δ = W x := div_mul_cancel₀ _ (ne_of_gt hδ)
      have hWpart : W x ≤ (W x / δ) * |y| := by
        calc W x = W x / δ * δ := hWeq.symm
          _ ≤ W x / δ * |y| := mul_le_mul_of_nonneg_left hyδ hdiv0
      have hfar : |SpectrallyNegativeLevy.generatorIntegrand W x y| ≤
          (W x / δ + |deriv W x|) * |y| := by
        calc
          |SpectrallyNegativeLevy.generatorIntegrand W x y|
              ≤ W x + |deriv W x| * min 1 |y| := hb2
          _ = W x + |deriv W x| * |y| := by rw [hmin]
          _ ≤ (W x / δ) * |y| + |deriv W x| * |y| := by linarith [hWpart]
          _ = (W x / δ + |deriv W x|) * |y| := by ring
      have hC2max : W x / δ + |deriv W x| ≤ K := by
        unfold K; exact le_max_of_le_left (le_max_of_le_right (le_refl _))
      have hCm : 0 ≤ |y| := abs_nonneg _
      rw [hmin]
      calc
        |SpectrallyNegativeLevy.generatorIntegrand W x y|
            ≤ (W x / δ + |deriv W x|) * |y| := hfar
        _ ≤ K * |y| := mul_le_mul_of_nonneg_right hC2max hCm
    · have hylt : |y| < δ := lt_of_not_ge hyδ
      have hyv : y ∈ v := hball (Metric.mem_ball.mpr (by
        rw [Real.dist_eq, sub_zero]; exact hylt))
      have hybound : |SpectrallyNegativeLevy.generatorIntegrand W x y| ≤ C * |y| :=
        hvs y hyv
      have hCmax : C ≤ K := by
        unfold K; exact le_max_of_le_left (le_max_of_le_left (le_refl _))
      have hCm : 0 ≤ |y| := abs_nonneg _
      rw [hmin]
      calc
        |SpectrallyNegativeLevy.generatorIntegrand W x y| ≤ C * |y| := hybound
        _ ≤ K * |y| := mul_le_mul_of_nonneg_right hCmax hCm
  · have hmin : min 1 |y| = 1 := min_eq_left (le_of_not_ge hsmall_y)
    have hb2 := hdecomp y hyneg
    calc
      |SpectrallyNegativeLevy.generatorIntegrand W x y|
          ≤ W x + |deriv W x| * min 1 |y| := hb2
      _ = W x + |deriv W x| * 1 := by rw [hmin]
      _ ≤ (W x + |deriv W x|) * 1 := by
          have : 0 ≤ W x + |deriv W x| := by
            linarith [hWx0, abs_nonneg (deriv W x)]
          linarith
      _ ≤ K * 1 := by
          have h2 : W x + |deriv W x| ≤ K := by
            unfold K; exact le_max_of_le_right (le_refl _)
          linarith [hK]
      _ = K * min 1 |y| := by rw [hmin]
