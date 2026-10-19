-- Prove2me | solution 2 for AvramDividend.Classical.barrierValue_generatorIntegrable_above
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T06:39:40.918146+00:00
-- url     : https://prove2.me/submissions/fb0ddbe0-5730-4a05-a44d-8711ef2d9d55

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_barrier_generatorIntegrand_zero_small_negative_jump_above
import Theorems.Thm_AvramDividend_Classical_generatorIntegrable_of_zero_near_and_bounded_tail
import Theorems.Thm_AvramDividend_Classical_levy_negative_mass_away_from_zero_finite
import Theorems.Thm_AvramDividend_Classical_barrierValue_bounded_on_left

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 ≤ a) (hx : a < x) :
    X.GeneratorIntegrable (barrierValue W a) x := by
  let v : ℝ → ℝ := barrierValue W a
  let d : EReal := scaleDeriv W a
  let c : ℝ := divE (W a) d
  let δ : ℝ := min 1 (x - a) / 2
  have hgap : 0 < x - a := sub_pos.mpr hx
  have hmin : 0 < min 1 (x - a) := lt_min (by norm_num) hgap
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδone : δ ≤ 1 := by
    dsimp [δ]; have hminle := min_le_left (1 : ℝ) (x - a); linarith
  have hδgap : δ ≤ x - a := by
    dsimp [δ]; have hminle := min_le_right (1 : ℝ) (x - a); linarith
  have hmono : Monotone W := by
    intro z w hzw
    by_cases hz : z < 0
    · rw [hW.1 z hz]
      by_cases hw : w < 0
      · rw [hW.1 w hw]
      · exact hW.2.1 w (le_of_not_gt hw)
    · have hz0 : 0 ≤ z := le_of_not_gt hz
      have hw0 : 0 ≤ w := hz0.trans hzw
      exact hW.2.2.2.1 (mem_Ici.mpr hz0) (mem_Ici.mpr hw0) hzw
  have hWmeas : Measurable W := hmono.measurable
  have hdivmeas : Measurable (fun z : ℝ => divE (W z) d) := by
    by_cases ht : d = ⊤
    · simp [divE, ht]
    · simp only [divE, if_neg ht]
      change Measurable (fun z : ℝ => W z / d.toReal)
      exact hWmeas.div measurable_const
  have hmid : Measurable (fun z : ℝ =>
        if z ≤ a then divE (W z) d else z - a + c) := by
    exact Measurable.ite measurableSet_Iic hdivmeas
      ((measurable_id.sub_const a).add_const c)
  have hvmeas : Measurable v := by
    change Measurable (fun z : ℝ =>
      if z < 0 then 0 else if z ≤ a then divE (W z) d else z - a + c)
    exact Measurable.ite measurableSet_Iio measurable_const hmid
  have hgintegrand : Measurable
      (SpectrallyNegativeLevy.generatorIntegrand v x) := by
    unfold SpectrallyNegativeLevy.generatorIntegrand
    have hshift : Measurable (fun y : ℝ => v (x + y)) :=
      hvmeas.comp (measurable_const.add measurable_id)
    have hind : Measurable (fun y : ℝ =>
        (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y) :=
      (measurable_const : Measurable (fun _ : ℝ => (1 : ℝ))).indicator measurableSet_Ioo
    exact (hshift.sub measurable_const).sub
      ((measurable_const.mul measurable_id).mul hind)
  have hloc : v =ᶠ[𝓝 x] (fun z : ℝ => z - a + c) := by
    filter_upwards [lt_mem_nhds hx] with z hz
    have hz0 : ¬ z < 0 := by linarith
    have hza : ¬ z ≤ a := by linarith
    simp [v, barrierValue, hz0, hza, c, d]
  have hd : deriv v x = 1 := by
    rw [hloc.deriv_eq]
    simp
  obtain ⟨B, hB, hvbound⟩ :=
    barrierValue_bounded_on_left W a x ha hx hW.2.1 hW.2.2.2.1
  have hfinite : X.ν (Iic (-δ)) < ⊤ :=
    levy_negative_mass_away_from_zero_finite X δ hδ
  have hzero : ∀ y, -δ < y → y < 0 →
      SpectrallyNegativeLevy.generatorIntegrand v x y = 0 := by
    intro y hy hy0
    have hy1 : -1 < y := by linarith
    have hxy : a < x + y := by linarith
    change SpectrallyNegativeLevy.generatorIntegrand (barrierValue W a) x y = 0
    exact barrier_generatorIntegrand_zero_small_negative_jump_above
      W a x y ha hx hxy hy1 hy0
  have hbound : ∀ y ∈ Iic (-δ),
      |SpectrallyNegativeLevy.generatorIntegrand v x y| ≤ 2 * B + 1 := by
    intro y hy
    have hyneg : y ≤ 0 := by
      have hh : y ≤ -δ := hy
      linarith
    have hdest : x + y ≤ x := by linarith
    have hb1 : |v (x + y)| ≤ B := hvbound (x + y) hdest
    have hb2 : |v x| ≤ B := hvbound x le_rfl
    have hindbound : |y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y| ≤ 1 := by
      by_cases hi : y ∈ Ioo (-1 : ℝ) 1
      · simpa only [Set.indicator_of_mem hi, Pi.one_apply, mul_one] using
          (abs_le.mpr ⟨le_of_lt hi.1, le_of_lt hi.2⟩)
      · simp [Set.indicator_of_notMem hi]
    have heq : SpectrallyNegativeLevy.generatorIntegrand v x y =
        v (x + y) - v x -
          y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y := by
      simp only [SpectrallyNegativeLevy.generatorIntegrand, hd, one_mul]
      all_goals rfl
    rw [heq]
    have ht : |v (x + y) - v x| ≤ |v (x + y)| + |v x| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        (abs_sub_le (v (x + y)) (0 : ℝ) (v x))
    have ht2 : |v (x + y) - v x -
        y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y| ≤
        |v (x + y) - v x| +
          |y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        (abs_sub_le (v (x + y) - v x) (0 : ℝ)
          (y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y))
    linarith
  exact generatorIntegrable_of_zero_near_and_bounded_tail
    X v x δ (2 * B + 1) hδ hgintegrand hfinite hbound hzero