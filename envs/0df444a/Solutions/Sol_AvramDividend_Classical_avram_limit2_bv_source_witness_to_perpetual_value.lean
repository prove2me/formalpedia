-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_bv_source_witness_to_perpetual_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T14:43:22.015738+00:00
-- url     : https://prove2.me/submissions/54bf4d03-368a-4f6f-978a-57a6e510ad04

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_strict_survival_preterminal_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_probability_real_grids_to_perpetual_value
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical
/-- Original-process source-grid witnesses bound genuine perpetual value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hSource : ∀ (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T),
      ∃ F M J : ℕ → Ω → ℝ,
        (∀ n, Measurable (F n)) ∧
        (∀ n, Integrable (F n) P) ∧
        (∀ n, 0 ≤ᵐ[P] F n) ∧
        (∀ n, Integrable (fun ω => M n ω + J n ω) P ∧
          (∫ ω, M n ω + J n ω ∂P) ≤ 0) ∧
        (∀ n, ∀ᵐ ω ∂P,
          F n ω ≤ w x + (M n ω + J n ω)) ∧
        (∀ᵐ ω ∂P,
          let S : ℝ≥0 := ⟨T, hT⟩
          ENNReal.ofReal
            ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
                ENNReal.ofReal (Real.exp (-(q * t)))
                  ∂(dividendMeasure D ω)).toReal +
              (if (S : ℝ≥0∞) < ruinTime X x D ω then
                Real.exp (-(q * T)) * w (riskProcess X x D S ω)
              else 0)) ≤
            liminf (fun n => ENNReal.ofReal (F n ω)) atTop)) :
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by
  apply avram_limit2_original_probability_real_grids_to_perpetual_value
    X q (le_of_lt hq) x D hD (w x)
  intro n
  let T : ℝ := (((n + 1 : ℕ) : ℝ))
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hTpos : 0 < T := by dsimp [T]; positivity
  obtain ⟨F, M, J, hFmeas, hFint, hFpos, hResidual,
    hPath, hFatou⟩ := hSource T hT hTpos
  let S : ℝ≥0 := ⟨T, hT⟩
  let Term : Ω → ℝ := fun ω =>
    if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω)
    else 0
  have hTermPos : ∀ᵐ ω ∂P, 0 ≤ Term ω := by
    apply Filter.Eventually.of_forall
    intro ω
    exact avram_limit2_original_strict_survival_preterminal_nonnegative
      X q x w D T hT hTpos hw_nonneg ω
  refine ⟨Term, F, (fun k ω => M k ω + J k ω),
    hTermPos, hFmeas, hFint, hFpos, ?_, ?_, ?_, ?_⟩
  · intro k
    exact (hResidual k).1
  · intro k
    exact hPath k
  · intro k
    exact (hResidual k).2
  · exact hFatou
