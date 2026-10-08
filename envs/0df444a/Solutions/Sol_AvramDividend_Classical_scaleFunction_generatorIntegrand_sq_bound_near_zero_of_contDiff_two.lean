-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generatorIntegrand_sq_bound_near_zero_of_contDiff_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T20:53:35.242185+00:00
-- url     : https://prove2.me/submissions/e59f065a-2a2a-44d7-a0ab-826c659358a4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (hx : x ∈ Ioo 0 a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a)) :
    ∃ r C : ℝ, 0 < r ∧ r ≤ min x 1 ∧ 0 ≤ C ∧
      ∀ y ∈ Ioo (-r) 0,
        ‖SpectrallyNegativeLevy.generatorIntegrand W x y‖ ≤
          C * y ^ 2 := by
  let r : ℝ := min x 1 / 2
  have hmin : 0 < min x 1 := lt_min hx.1 one_pos
  have hr : 0 < r := by
    dsimp [r]
    linarith
  have hrlt : r < min x 1 := by
    dsimp [r]
    linarith
  have hrle : r ≤ min x 1 := hrlt.le
  have hrx : r < x := lt_of_lt_of_le hrlt (min_le_left x 1)
  have hr1 : r ≤ 1 := hrle.trans (min_le_right x 1)
  let K : Set ℝ := Icc (x - r) x
  have hKsub : K ⊆ Ioo 0 a := by
    intro z hz
    change z ∈ Icc (x - r) x at hz
    constructor
    · exact lt_of_lt_of_le (sub_pos.mpr hrx) hz.1
    · exact lt_of_le_of_lt hz.2 hx.2
  have hC2K : ContDiffOn ℝ 2 W K := hC2.mono hKsub
  have huniqK : UniqueDiffOn ℝ K := by
    dsimp [K]
    exact uniqueDiffOn_Icc (by linarith)
  have hcont :
      ContinuousOn
        (fun z => ‖iteratedDerivWithin 2 W K z‖) K := by
    exact
      (ContDiffOn.continuousOn_iteratedDerivWithin
        hC2K (by norm_num) huniqK).norm
  have hKne : K.Nonempty := by
    refine ⟨x, ?_⟩
    change x ∈ Icc (x - r) x
    exact ⟨by linarith, le_rfl⟩
  obtain ⟨zM, hzM, hmax⟩ :
      ∃ zM ∈ K, ∀ z ∈ K,
        ‖iteratedDerivWithin 2 W K z‖ ≤
          ‖iteratedDerivWithin 2 W K zM‖ :=
    isCompact_Icc.exists_isMaxOn hKne hcont
  let C : ℝ := ‖iteratedDerivWithin 2 W K zM‖
  have hC : 0 ≤ C := by
    dsimp [C]
    exact abs_nonneg _
  refine ⟨r, C, hr, hrle, hC, ?_⟩
  intro y hy
  have hy0 : y < 0 := hy.2
  have hyr : -r < y := hy.1
  have horder : x + y ≤ x := by linarith
  have hxy0 : 0 < x + y := by linarith
  have hsegsub : uIcc x (x + y) ⊆ Ioo 0 a := by
    intro z hz
    rw [uIcc_of_ge horder] at hz
    exact ⟨lt_of_lt_of_le hxy0 hz.1, lt_of_le_of_lt hz.2 hx.2⟩
  have hsegC2 : ContDiffOn ℝ 2 W (uIcc x (x + y)) :=
    hC2.mono hsegsub
  have hneq : x ≠ x + y := by linarith
  obtain ⟨z, hz, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := W) (x₀ := x) (x := x + y) (n := 1) hneq hsegC2
  have huniqSeg : UniqueDiffOn ℝ (uIcc x (x + y)) :=
    uniqueDiffOn_uIcc hneq
  have hxC1 : ContDiffAt ℝ 1 W x :=
    (hC2.contDiffAt (isOpen_Ioo.mem_nhds hx)).of_le (by norm_num)
  have hder :
      iteratedDerivWithin 1 W (uIcc x (x + y)) x = deriv W x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv huniqSeg hxC1 left_mem_uIcc]
    simp
  have htaylor :
      taylorWithinEval W 1 (uIcc x (x + y)) x (x + y) =
        W x + deriv W x * y := by
    rw [show (1 : ℕ) = 0 + 1 by rfl, taylorWithinEval_succ]
    simp [hder, smul_eq_mul]
    ring
  have hzK : z ∈ K := by
    rw [uIoo_of_ge horder] at hz
    change z ∈ Icc (x - r) x
    have hleft : x - r < x + y := by linarith
    exact ⟨(hleft.trans hz.1).le, hz.2.le⟩
  have hzC2 : ContDiffAt ℝ 2 W z :=
    hC2.contDiffAt (isOpen_Ioo.mem_nhds (hKsub hzK))
  have hzEq :
      iteratedDerivWithin 2 W K z = iteratedDeriv 2 W z :=
    iteratedDerivWithin_eq_iteratedDeriv huniqK hzC2 hzK
  have hzbound : ‖iteratedDeriv 2 W z‖ ≤ C := by
    dsimp [C]
    rw [← hzEq]
    exact hmax z hzK
  have hyI : y ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · linarith [hr1, hyr]
    · linarith [hy0]
  rw [Real.norm_eq_abs]
  unfold SpectrallyNegativeLevy.generatorIntegrand
  rw [indicator_of_mem hyI]
  simp only [Pi.one_apply, mul_one]
  have hlinear :
      W (x + y) - W x - deriv W x * y =
        W (x + y) -
          taylorWithinEval W 1 (uIcc x (x + y)) x (x + y) := by
    rw [htaylor]
    ring
  rw [hlinear, hrem]
  simp only [one_add_one_eq_two, Nat.factorial_two, Nat.cast_ofNat]
  rw [show x + y - x = y by ring]
  rw [abs_div, abs_mul, abs_pow, sq_abs]
  norm_num
  have hzbound' : |iteratedDeriv 2 W z| ≤ C := by
    simpa [Real.norm_eq_abs] using hzbound
  have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
  have hhalf : |iteratedDeriv 2 W z| / 2 ≤ C := by
    nlinarith [hzbound', abs_nonneg (iteratedDeriv 2 W z)]
  calc
    |iteratedDeriv 2 W z| * y ^ 2 / 2 =
        (|iteratedDeriv 2 W z| / 2) * y ^ 2 := by ring
    _ ≤ C * y ^ 2 := mul_le_mul_of_nonneg_right hhalf hy2
