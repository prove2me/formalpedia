-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_uniform_near_jump_linear_bound_on_compact_C1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:01:06.760114+00:00
-- url     : https://prove2.me/submissions/dcbac823-cb38-43f1-86d4-b0cd481714cd

import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A compact C1 derivative bound yields uniform linear jump control near zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC1 : ContDiffOn ℝ 1 W (Ioo 0 a)) :
    ∃ r C : ℝ, 0 < r ∧ r < 1 ∧ r < l ∧ 0 ≤ C ∧
      ∀ x ∈ Icc l u, ∀ y ∈ Ioo (-r) 0,
        ‖SpectrallyNegativeLevy.generatorIntegrand W x y‖ ≤
          C * |y| := by
  let r : ℝ := min l 1 / 2
  have hmin0 : 0 < min l 1 := lt_min hl one_pos
  have hmin1 : min l 1 ≤ 1 := min_le_right _ _
  have hminl : min l 1 ≤ l := min_le_left _ _
  have hr : 0 < r := div_pos hmin0 (by norm_num)
  have hrlt1 : r < 1 := by
    dsimp [r]
    have h : min l 1 / 2 ≤ (1 : ℝ) / 2 :=
      (div_le_div_of_nonneg_right hmin1 (by norm_num))
    linarith
  have hrltl : r < l := by
    dsimp [r]
    have h : min l 1 / 2 ≤ l / 2 :=
      (div_le_div_of_nonneg_right hminl (by norm_num))
    linarith
  have hKlt : l - r < u := by linarith
  have hsub : Icc (l-r) u ⊆ Ioo 0 a := by
    intro z hz
    exact ⟨lt_of_lt_of_le (sub_pos.mpr hrltl) hz.1,
      lt_of_le_of_lt hz.2 hu⟩
  have hcontD0 : ContinuousOn (deriv W) (Icc (l-r) u) :=
    (hC1.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono hsub
  have hcontD : ContinuousOn (fun z : ℝ => |deriv W z|) (Icc (l-r) u) :=
    hcontD0.norm
  have hKne : (Icc (l-r) u).Nonempty :=
    ⟨u, ⟨hKlt.le, le_rfl⟩⟩
  obtain ⟨zM, hzM, hmax⟩ :
      ∃ zM ∈ Icc (l-r) u, ∀ z ∈ Icc (l-r) u,
        |deriv W z| ≤ |deriv W zM| :=
    isCompact_Icc.exists_isMaxOn hKne hcontD
  let D : ℝ := |deriv W zM|
  have hD : 0 ≤ D := abs_nonneg _
  have hder : ∀ z ∈ Icc (l-r) u, |deriv W z| ≤ D := hmax
  refine ⟨r, D + D, hr, hrlt1, hrltl, add_nonneg hD hD, ?_⟩
  intro x hx y hy
  have hy0 : y < 0 := hy.2
  have hxy0 : 0 < x + y := by linarith [hx.1, hy.1]
  have hsegsub : Icc (x+y) x ⊆ Ioo 0 a := by
    intro z hz
    exact ⟨lt_of_lt_of_le hxy0 hz.1, lt_of_le_of_lt hz.2 (hx.2.trans_lt hu)⟩
  have hsegC1 : ContDiffOn ℝ 1 W (Icc (x+y) x) := hC1.mono hsegsub
  have hsegdiff : DifferentiableOn ℝ W (Ioo (x+y) x) :=
    (hC1.differentiableOn (by norm_num)).mono
      (show Ioo (x+y) x ⊆ Ioo 0 a by
        intro z hz
        exact ⟨lt_of_lt_of_le hxy0 hz.1.le,
          lt_of_le_of_lt hz.2.le (hx.2.trans_lt hu)⟩)
  obtain ⟨z, hz, hslope⟩ :=
    exists_deriv_eq_slope W (by linarith) hsegC1.continuousOn hsegdiff
  have hzK : z ∈ Icc (l-r) u := by
    change z ∈ Ioo (x+y) x at hz
    constructor
    · linarith [hx.1, hy.1, hz.1]
    · exact le_trans hz.2.le hx.2
  have hxK : x ∈ Icc (l-r) u := ⟨by linarith [hx.1, hr], hx.2⟩
  have hzy : deriv W z * y = W (x + y) - W x := by
    have hne : (x - (x + y) : ℝ) ≠ 0 := by linarith
    have hdz : deriv W z = (W x - W (x+y)) / (x - (x+y)) := hslope
    have hzy' : deriv W z * (x+y-x) = W (x+y) - W x := by
      rw [hdz]; field_simp; ring_nf
    convert hzy' using 1 <;> ring
  have hyr : -r < y := hy.1
  have hyI : y ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hyr, hrlt1], by linarith [hy0]⟩
  have hcomp :
      ‖SpectrallyNegativeLevy.generatorIntegrand W x y‖ =
        |W (x+y) - W x - deriv W x * y| := by
    rw [Real.norm_eq_abs]
    unfold SpectrallyNegativeLevy.generatorIntegrand
    rw [indicator_of_mem hyI]
    simp only [Pi.one_apply, mul_one]
  have hdb : |deriv W z| + |deriv W x| ≤ D + D :=
    add_le_add (hder z hzK) (hder x hxK)
  calc
    ‖SpectrallyNegativeLevy.generatorIntegrand W x y‖ =
        |W (x+y) - W x - deriv W x * y| := hcomp
    _ ≤ |W (x+y) - W x| + |deriv W x * y| := abs_sub _ _
    _ = |deriv W z| * |y| + |deriv W x| * |y| := by
      rw [←hzy, abs_mul, abs_mul]
    _ = (|deriv W z| + |deriv W x|) * |y| := by ring
    _ ≤ (D+D) * |y| :=
      mul_le_mul_of_nonneg_right hdb (abs_nonneg y)
