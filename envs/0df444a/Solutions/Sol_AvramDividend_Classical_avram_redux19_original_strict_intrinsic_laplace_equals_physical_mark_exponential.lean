-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux19_original_strict_intrinsic_laplace_equals_physical_mark_exponential
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:17:29.162539+00:00
-- url     : https://prove2.me/submissions/6e546af0-2171-435e-a8d4-587ff0c0d42f

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_intrinsic_marked_magnitude_finite_sum
import Theorems.Thm_AvramDividend_Classical_avram_redux19_finite_nonnegative_marked_sum_real_exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-! Identify the strict intrinsic source Laplace variable with actual jump marks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (k : ℕ) :
    let S : Finset ℝ≥0 :=
      (AvramDividend.Classical.avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
    Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ T ∧ p.2 < -(1 / ((k : ℝ) + 1))
      then ENNReal.ofReal (-p.2) else 0
      ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) =
      Real.exp (∑ u ∈ S, (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) := by
  classical
  let J : Set ℝ≥0 := {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u <
      -(1 / ((k : ℝ) + 1))}
  have hFin : J.Finite :=
    AvramDividend.Classical.avram_redux19_original_strict_negative_marked_times_finite X ω T k
  let S : Finset ℝ≥0 := hFin.toFinset
  have hnonneg : ∀ u ∈ S,
      0 ≤ -(X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) := by
    intro u hu
    have hJ : u ∈ J := (hFin.mem_toFinset).mp hu
    have hc : -(1 / ((k : ℝ) + 1)) ≤ 0 :=
      neg_nonpos.mpr (by positivity)
    exact neg_nonneg.mpr (le_trans (le_of_lt hJ.2.2) hc)
  have hsource := AvramDividend.Classical.avram_redux19_original_strict_intrinsic_marked_magnitude_finite_sum X ω T k
  change (∫⁻ p : ℝ≥0 × ℝ,
    if 0 < p.1 ∧ p.1 ≤ T ∧ p.2 < -(1 / ((k : ℝ) + 1))
    then ENNReal.ofReal (-p.2) else 0
    ∂((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
    ∑ u ∈ S, ENNReal.ofReal (-(X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) at hsource
  rw [hsource]
  have h := AvramDividend.Classical.avram_redux19_finite_nonnegative_marked_sum_real_exponential
    S (fun u => -(X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) hnonneg
  have hS : S =
      (AvramDividend.Classical.avram_redux19_original_strict_negative_marked_times_finite
        X ω T k).toFinset := by
    ext u
    simp only [S, Set.Finite.mem_toFinset]
    rfl
  rw [hS] at h
  simpa only [neg_neg] using h
