-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB261_original_good_dividend_cell_fixed_level_gaussian_hit_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:53:32.951978+00:00
-- url     : https://prove2.me/submissions/3c31b088-c3ed-4af9-8fcf-375a0bac9018

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB256b_independent_gaussian_random_interval_with_source_density
import Theorems.Thm_AvramDividend_Classical_avram_gbB258_original_future_increment_indep_prepayment_reserve_centre
import Theorems.Thm_AvramDividend_Classical_avram_gbB260_original_good_dividend_cell_reserve_hit_forces_small_gaussian_increment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (s t u : ℝ≥0) (hst : s ≤ t) (htu : t < u)
    (x b epsilon : ℝ) (hEps : 0 ≤ epsilon)
    (mu : ℝ) (v : ℝ≥0) (hv : 0 < v)
    (hLaw : Measure.map (fun ω => X.X t ω - X.X s ω) P = gaussianReal mu v) :
    P {ω | D u ω - D s ω ≤ epsilon ∧
      x + X.X t ω - rightLimit D t ω = b} ≤
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹) *
        ENNReal.ofReal epsilon := by
  have ht : Measurable (X.X t) := (X.adapted t).mono (𝓕.le t) le_rfl
  have hs : Measurable (X.X s) := (X.adapted s).mono (𝓕.le s) le_rfl
  have hd : Measurable (D s) := (hD.2.2.2 s).mono (𝓕.le s) le_rfl
  have hCentre : Measurable (fun ω => b - x - X.X s ω + D s ω) := by
    fun_prop
  have hZ : Measurable (fun ω => X.X t ω - X.X s ω) := ht.sub hs
  have hInd : IndepFun (fun ω => b - x - X.X s ω + D s ω)
      (fun ω => X.X t ω - X.X s ω) P :=
    by
      apply (IndepFun_iff_Indep _ _ P).2
      exact (avram_gbB258_original_future_increment_indep_prepayment_reserve_centre
        X D hD s t hst x b).symm
  have hBig := avram_gbB256b_independent_gaussian_random_interval_with_source_density P
    (fun ω => b - x - X.X s ω + D s ω)
    (fun ω => X.X t ω - X.X s ω)
    hCentre hZ mu v hv hLaw hInd epsilon hEps
  have hSub : {ω | D u ω - D s ω ≤ epsilon ∧
        x + X.X t ω - rightLimit D t ω = b} ⊆
      {ω | (b - x - X.X s ω + D s ω) ≤ (X.X t ω - X.X s ω) ∧
        (X.X t ω - X.X s ω) ≤ (b - x - X.X s ω + D s ω) + epsilon} := by
    intro ω hω
    exact avram_gbB260_original_good_dividend_cell_reserve_hit_forces_small_gaussian_increment X D hD ω s t u hst htu x b epsilon hω.1 hω.2
  exact (measure_mono hSub).trans hBig
