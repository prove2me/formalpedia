-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux12b_original_jump_laplace_finite_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:22:49.575199+00:00
-- url     : https://prove2.me/submissions/7389a055-0638-469f-a327-5e1443df2461

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_lintegral_eq_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_redux17_original_intrinsic_marked_cutoff_laplace
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Reduce actual source-jump cutoff Laplace evaluation to its intrinsic marked
counting measure and the original pathwise marked sum identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ (n k : ℕ),
      (∫ ω : Ω, Real.exp (-((∑' v : ℝ≥0,
        if 0 < v ∧ v ≤ (n : ℝ≥0) ∧
          (1 / ((k : ℝ) + 1)) < (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal)) ∂P) =
      Real.exp (-((n : ℝ) *
        (∫ y in Iio (-(1 / ((k : ℝ) + 1))), (1 - Real.exp y) ∂X.ν))) := by
  intro n k
  let ε : ℝ := 1 / ((k : ℝ) + 1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  let F : (ℝ≥0 × ℝ) → ℝ≥0∞ := fun p =>
    if 0 < p.1 ∧ p.1 ≤ (n : ℝ≥0) ∧ p.2 < -ε then
      ENNReal.ofReal (-p.2) else 0
  have hS : MeasurableSet {p : ℝ≥0 × ℝ |
      0 < p.1 ∧ p.1 ≤ (n : ℝ≥0) ∧ p.2 < -ε} := by
    have hfst : Measurable (fun p : ℝ≥0 × ℝ => p.1) := measurable_fst
    have hsnd : Measurable (fun p : ℝ≥0 × ℝ => p.2) := measurable_snd
    have ha : MeasurableSet {p : ℝ≥0 × ℝ | (0 : ℝ≥0) < p.1} :=
      measurableSet_lt (measurable_const : Measurable
        (fun _ : ℝ≥0 × ℝ => (0 : ℝ≥0))) hfst
    have hb : MeasurableSet {p : ℝ≥0 × ℝ | p.1 ≤ (n : ℝ≥0)} :=
      measurableSet_le hfst (measurable_const : Measurable
        (fun _ : ℝ≥0 × ℝ => (n : ℝ≥0)))
    have hc : MeasurableSet {p : ℝ≥0 × ℝ | p.2 < -ε} :=
      measurableSet_lt hsnd (measurable_const : Measurable
        (fun _ : ℝ≥0 × ℝ => (-ε : ℝ)))
    simpa only [Set.setOf_and] using ha.inter (hb.inter hc)
  have hF : Measurable F := by
    dsimp only [F]
    have hmark : Measurable (fun p : ℝ≥0 × ℝ =>
        ENNReal.ofReal (-p.2)) := by
      fun_prop
    exact hmark.ite hS measurable_const
  let J : Ω → ℝ≥0 → ℝ := fun ω u =>
    Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
  have hpoint (ω : Ω) :
      (∫⁻ p, F p ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
      ∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ (n : ℝ≥0) ∧ ε < J ω u then
          ENNReal.ofReal (J ω u) else 0 := by
    rw [avram_wave4_04a_actual_intrinsic_lintegral_eq_jump_sum X ω F hF]
    apply tsum_congr
    intro u
    have hs : X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = -J ω u := by
      dsimp [J]
      ring
    have hc : (X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < -ε) ↔
        ε < J ω u := by
      rw [hs]
      constructor <;> intro h <;> linarith
    by_cases hu : 0 < u
    · by_cases ht : u ≤ (n : ℝ≥0)
      · by_cases hj : ε < J ω u
        · have hnonzero : X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 := by
            rw [hs]
            exact neg_ne_zero.mpr (ne_of_gt (lt_trans hε hj))
          have hmark := hc.mpr hj
          simp [F, hu, ht, hj, hnonzero, hmark, hs] <;> aesop
        · have hmark : ¬ (X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < -ε) :=
            fun h => hj (hc.mp h)
          simp [F, hu, ht, hj, hmark]
      · simp [F, hu, ht]
    · simp [F, hu]
  have hchild :=
    avram_redux17_original_intrinsic_marked_cutoff_laplace X hX hBV n k
  calc
    (∫ ω : Ω, Real.exp (-((∑' v : ℝ≥0,
        if 0 < v ∧ v ≤ (n : ℝ≥0) ∧
          (1 / ((k : ℝ) + 1)) <
              (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal)) ∂P) =
      (∫ ω : Ω, Real.exp (-((∫⁻ p, F p ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) ∂P) := by
      apply integral_congr_ae
      filter_upwards [] with ω
      simpa only [J, ε] using
        congrArg (fun t : ℝ≥0∞ => Real.exp (-(t.toReal))) (hpoint ω).symm
    _ = Real.exp (-((n : ℝ) *
        (∫ y in Iio (-(1 / ((k : ℝ) + 1))), (1 - Real.exp y) ∂X.ν))) := by
      simpa only [F, ε] using hchild
