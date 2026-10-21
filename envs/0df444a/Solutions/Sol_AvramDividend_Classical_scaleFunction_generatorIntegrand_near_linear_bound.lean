-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generatorIntegrand_near_linear_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T03:55:24.233989+00:00
-- url     : https://prove2.me/submissions/938f97d0-1a7c-4628-8e35-1ce85d815e02

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a x : ℝ)
    (hC1 : ContDiffOn ℝ 1 W (Ioo 0 a))
    (hx : x ∈ Ioo 0 a) :
    ∃ r C : ℝ, 0 < r ∧ r < 1 ∧ r < x ∧ 0 ≤ C ∧
      ∀ y ∈ Ioo (-r) 0,
        |SpectrallyNegativeLevy.generatorIntegrand W x y| ≤
          C * |y| := by
  have hx0 : 0 < x := hx.1
  -- The radius: small enough that `[x - r, x]` stays inside the C1
  -- region, and such that `-1 < y < 1` on the range under consideration.
  let r : ℝ := min (min x 1) (a - x) / 2
  have hmin0 : 0 < min (min x 1) (a - x) :=
    lt_min (lt_min hx0 one_pos) (sub_pos.mpr hx.2)
  have hmin1 : min (min x 1) (a - x) ≤ 1 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hminx : min (min x 1) (a - x) ≤ x := le_trans (min_le_left _ _) (min_le_left _ _)
  have hr : 0 < r := by
    dsimp [r]
    exact div_pos hmin0 (by norm_num)
  have hrlt1 : r < 1 := by
    dsimp [r]
    have h2 : min (min x 1) (a - x) ≤ 1 := hmin1
    have h3 : min (min x 1) (a - x) / 2 ≤ 1 / 2 := by
      refine (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2 ?_
      linarith
    have h4 : (1 : ℝ) / 2 < 1 := by norm_num
    exact lt_of_le_of_lt h3 h4
  have hrltx : r < x := by
    dsimp [r]
    have h2 : min (min x 1) (a - x) ≤ x := hminx
    have h3 : min (min x 1) (a - x) / 2 ≤ x / 2 := by
      refine (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2 ?_
      linarith
    have h4 : (x : ℝ) / 2 < x := by
      have : (0 : ℝ) < x := hx0
      linarith
    exact lt_of_le_of_lt h3 h4
  -- The derivative is bounded on the compact `[x - r, x]`.
  let K : Set ℝ := Icc (x - r) x
  have hKsub : K ⊆ Ioo 0 a := by
    intro z hz
    change z ∈ Icc (x - r) x at hz
    constructor
    · exact lt_of_lt_of_le (sub_pos.mpr hrltx) hz.1
    · exact lt_of_le_of_lt hz.2 hx.2
  have hcontderiv0 : ContinuousOn (deriv W) K :=
    (hC1.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono hKsub
  have hcontderiv : ContinuousOn (fun z : ℝ => |deriv W z|) K := hcontderiv0.norm
  have hKne : K.Nonempty := by
    refine ⟨x, ?_⟩
    change x ∈ Icc (x - r) x
    exact ⟨by linarith, le_rfl⟩
  obtain ⟨zM, hzM, hmax⟩ :
      ∃ zM ∈ K, ∀ z ∈ K, |deriv W z| ≤ |deriv W zM| :=
    isCompact_Icc.exists_isMaxOn hKne hcontderiv
  let C : ℝ := |deriv W zM| + |deriv W x|
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hdx : |deriv W x| ≤ C := by
    dsimp [C]
    linarith [abs_nonneg (deriv W zM)]
  refine ⟨r, C, hr, hrlt1, hrltx, hC0, ?_⟩
  intro y hy
  have hy0 : y < 0 := hy.2
  have hyr : -r < y := hy.1
  have hxy0 : 0 < x + y := by linarith
  -- The mean value theorem on the segment `[x + y, x]`.
  have hsegsub : Icc (x + y) x ⊆ Ioo 0 a := by
    intro z hz
    exact ⟨lt_of_lt_of_le hxy0 hz.1, lt_of_le_of_lt hz.2 hx.2⟩
  have hsegC1 : ContDiffOn ℝ 1 W (Icc (x + y) x) := hC1.mono hsegsub
  have hsegdiff : DifferentiableOn ℝ W (Ioo (x + y) x) :=
    (hC1.differentiableOn (by norm_num)).mono
      (show Ioo (x + y) x ⊆ Ioo 0 a by
        intro z hz
        exact ⟨lt_of_lt_of_le hxy0 hz.1.le, lt_of_le_of_lt hz.2.le hx.2⟩)
  obtain ⟨z, hz, hslope⟩ :=
    exists_deriv_eq_slope W (by linarith) hsegC1.continuousOn hsegdiff
  have hzK : z ∈ K := by
    change z ∈ Ioo (x + y) x at hz
    change z ∈ Icc (x - r) x
    have hleft : x - r < x + y := by linarith
    exact ⟨le_of_lt (hleft.trans hz.1), le_of_lt hz.2⟩
  have hzbound : |deriv W z| ≤ C := by
    dsimp [C]
    have h1 : |deriv W z| ≤ |deriv W zM| := hmax z hzK
    exact le_trans h1 (le_add_of_nonneg_right (abs_nonneg (deriv W x)))
  have hzy : deriv W z * (x + y - x) = W (x + y) - W x := by
    have hne : (x - (x + y) : ℝ) ≠ 0 := by linarith
    have hdz : deriv W z = (W x - W (x + y)) / (x - (x + y)) := hslope
    rw [hdz]; field_simp; ring_nf
  rw [show x + y - x = y by ring] at hzy
  -- On the range `-r < y < 0` with `r < 1`, the compensation indicator is `1`.
  have hyI : y ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hcomp : |SpectrallyNegativeLevy.generatorIntegrand W x y|
      = |W (x + y) - W x - deriv W x * y| := by
    unfold SpectrallyNegativeLevy.generatorIntegrand
    rw [indicator_of_mem hyI]
    simp only [Pi.one_apply, mul_one]
  have htri : |W (x + y) - W x - deriv W x * y|
      ≤ |W (x + y) - W x| + |deriv W x * y| := abs_sub _ _
  have hyabs : 0 ≤ |y| := abs_nonneg y
  have h1 : |W (x + y) - W x| = |deriv W z * y| := by rw [hzy]
  have h2 : |deriv W x * y| = |deriv W x| * |y| := by rw [abs_mul]
  have h3 : |deriv W z| * |y| + |deriv W x| * |y|
      = (|deriv W z| + |deriv W x|) * |y| := by ring
  have h4 : |deriv W z| + |deriv W x| ≤ C := by
    dsimp [C]
    have h5 : |deriv W z| ≤ |deriv W zM| := hmax z hzK
    exact add_le_add h5 (le_refl _)
  have h5 : (|deriv W z| + |deriv W x|) * |y| ≤ C * |y| :=
    mul_le_mul_of_nonneg_right h4 hyabs
  calc
    |SpectrallyNegativeLevy.generatorIntegrand W x y| =
        |W (x + y) - W x - deriv W x * y| := hcomp
    _ ≤ |W (x + y) - W x| + |deriv W x * y| := htri
    _ = |deriv W z * y| + |deriv W x| * |y| := by rw [h1, h2]
    _ = |deriv W z| * |y| + |deriv W x| * |y| := by rw [abs_mul]
    _ = (|deriv W z| + |deriv W x|) * |y| := h3
    _ ≤ C * |y| := h5
