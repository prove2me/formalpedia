-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04_parent_bv_zero_cap_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T01:24:29.091768+00:00
-- url     : https://prove2.me/submissions/bd6c11ad-5445-46f3-bc97-88e5ba72accb

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_admissibleLe_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_initial_dividendMeasure_atom_formula
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Theorems.Thm_AvramDividend_Classical_truncated_dividend_payoff_at_zero_eq_initial_atom
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q x : ℝ) (hq : 0 < q) (hx : 0 < x) :
    ∃ (w : ℝ → ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ) (T : ℝ),
      ContinuousOn w (Ici 0) ∧ (∀ y < 0, w y = 0) ∧
      ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
        X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) ∧
      IsAdmissibleLe X x C D ∧
      (∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω →
        0 ≤ w (riskProcess X x D t ω)) ∧
      0 ≤ T ∧
      ¬ ((∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) := by
  let D : ℝ≥0 → Ω → ℝ := barrierStrategy X x 0
  have hD : IsAdmissibleLe X x (0 : ℝ≥0∞) D := by
    simpa [D] using (barrierStrategy_admissibleLe_nonnegative_barrier
      X x 0 (le_of_lt hx) (le_refl 0))
  have hStrat : IsDividendStrategy 𝓕 D := hD.1.1
  have hAt (ω : Ω) :
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      ENNReal.ofReal x := by
    calc
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
          ENNReal.ofReal (rightLimit D 0 ω - D 0 ω) :=
        truncated_dividend_payoff_at_zero_eq_initial_atom
          D hStrat q (ruinTime X x D ω) ω
      _ = dividendMeasure D ω ({0} : Set ℝ) := by
        symm
        simpa using dividendMeasure_singleton_eq_rightLimit_sub D hStrat ω 0
      _ = ENNReal.ofReal (max 0 (x - 0)) := by
        simpa [D] using (barrierStrategy_initial_dividendMeasure_atom_formula
          X x 0 (le_of_lt hx) (le_refl 0) ω)
      _ = ENNReal.ofReal x := by simp [le_of_lt hx]
  letI : IsProbabilityMeasure P := X.isProbability
  have hCash :
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
      ENNReal.ofReal x := by simp_rw [hAt]; simp
  refine ⟨fun _ => 0, 0, D, 0, ?_, ?_, ?_, ?_, ?_, hD, ?_, le_rfl, ?_⟩
  · exact continuousOn_const
  · intro y hy; rfl
  · have he : {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (0 : ℝ≥0∞)} =
        (∅ : Set ℝ) := by ext y; simp
    simp [he]
  · intro y hy hyC; simp at hyC
  · intro y hy hyC; simp at hyC
  · intro ω t ht hruin; simp
  · intro hFalse
    have hPos : (0 : ℝ≥0∞) < ENNReal.ofReal x := ENNReal.ofReal_pos.mpr hx
    have hh : ENNReal.ofReal x ≤ (0 : ℝ≥0∞) := by
      simpa [hCash] using hFalse
    exact (not_le_of_gt hPos) hh
