-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux20_original_strict_marked_cutoff_laplace_finite_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:12:09.356261+00:00
-- url     : https://prove2.me/submissions/da153c0a-b50c-4e10-be63-3948ed77cefc

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_redux20_original_strict_marked_borel_weight_finite_sum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-! The source-exact original marked cutoff Laplace factor is a finite product. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (k : ℕ) :
    let S : Finset ℝ≥0 :=
      (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
    Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ T ∧ p.2 < -(1 / ((k : ℝ) + 1))
      then ENNReal.ofReal (-p.2) else 0
      ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) =
    ∏ u ∈ S, Real.exp (X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) := by
  classical
  let J : Set ℝ≥0 := {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u <
      -(1 / ((k : ℝ) + 1))}
  have hFin : J.Finite :=
    avram_redux19_original_strict_negative_marked_times_finite X ω T k
  let S : Finset ℝ≥0 := hFin.toFinset
  let δ : ℝ≥0 → ℝ := fun u => X.X u ω -
    Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  have hneg : ∀ u ∈ S, δ u < 0 := by
    intro u hu
    have hJ : u ∈ J := (hFin.mem_toFinset).mp hu
    change 0 < u ∧ u ≤ T ∧ δ u < -(1 / ((k : ℝ) + 1)) at hJ
    exact lt_of_lt_of_le hJ.2.2 (neg_nonpos.mpr (by positivity))
  have hnonneg : ∀ u ∈ S, 0 ≤ -(δ u) := by
    intro u hu
    exact neg_nonneg.mpr (le_of_lt (hneg u hu))
  have hmeas : Measurable (fun y : ℝ => ENNReal.ofReal (-y)) :=
    ENNReal.measurable_ofReal.comp measurable_neg
  have hmark := avram_redux20_original_strict_marked_borel_weight_finite_sum
    X ω T k (fun y => ENNReal.ofReal (-y)) hmeas
  have hfinite : ∀ u ∈ S, ENNReal.ofReal (-(δ u)) ≠ ⊤ := by
    intro u hu
    exact ENNReal.ofReal_ne_top
  have hsum := ENNReal.toReal_sum (s := S)
    (f := fun u => ENNReal.ofReal (-(δ u))) hfinite
  have hreal : (∑ u ∈ S, ENNReal.ofReal (-(δ u))).toReal =
      ∑ u ∈ S, -(δ u) := by
    rw [hsum]
    apply Finset.sum_congr rfl
    intro u hu
    exact ENNReal.toReal_ofReal (hnonneg u hu)
  change Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
    if 0 < p.1 ∧ p.1 ≤ T ∧ p.2 < -(1 / ((k : ℝ) + 1))
    then ENNReal.ofReal (-p.2) else 0
    ∂((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) =
    ∏ u ∈ S, Real.exp (δ u)
  rw [hmark, hreal]
  have hneg_sum : -(∑ u ∈ S, -(δ u)) = ∑ u ∈ S, δ u := by
    simp only [Finset.sum_neg_distrib, neg_neg]
  rw [hneg_sum]
  exact Real.exp_sum S δ
