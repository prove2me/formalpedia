-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_countable_nonnegative_predictable_real_l1_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:26:25.356109+00:00
-- url     : https://prove2.me/submissions/d28e0f0d-3bb3-4190-a4f0-ae3567bd4311

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_countable_predictable_weighted_rate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- A countable nonnegative genuine predictable-simple marked count has a
real L¹ representative with the expected rate when total ν-intensity is finite. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℕ → ℝ≥0) (hst : ∀ i, s i ≤ t i)
    (B : ℕ → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (W : ℕ → Ω → ℝ≥0∞)
    (hW : ∀ i, Measurable[𝓕 (s i)] (W i))
    (hRate : ∀ i, (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i) ∂P) = (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)))
    (hSumRate : (∑' i, (∫⁻ ω, W i ω ∂P) * (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))) < ⊤) :
    let total : Ω → ℝ≥0∞ := fun ω => ∑' i, W i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i)
    let rateTotal : ℝ≥0∞ := ∑' i, (∫⁻ ω, W i ω ∂P) * (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))
    Integrable (fun ω => (total ω).toReal) P ∧
      (∫ ω, (total ω).toReal ∂P) = rateTotal.toReal := by
  dsimp only
  have hMeas (i : ℕ) : Measurable (fun ω : Ω => W i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i)) :=
    ((hW i).mono (𝓕.le (s i)) le_rfl).mul
      (avram_p2_e_compensator_intrinsic_rectangle_count_measurable
        X (s i) (t i) (hst i) (B i) (hB i))
  have hSumMeas : Measurable (fun ω : Ω => ∑' i, W i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i)) :=
    Measurable.tsum hMeas
  have hRateTotal := avram_p2_e_compensator_countable_predictable_weighted_rate
    X s t hst B hB W hW hRate
  have hFinite : (∫⁻ ω, ∑' i, W i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i) ∂P) ≠ ⊤ := by
    rw [hRateTotal]
    exact ne_of_lt hSumRate
  have hInt := integrable_toReal_of_lintegral_ne_top hSumMeas.aemeasurable hFinite
  constructor
  · exact hInt
  · calc
      (∫ ω, (∑' i, W i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i)).toReal ∂P) =
        (∫⁻ ω, ∑' i, W i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i) ∂P).toReal :=
          integral_toReal hSumMeas.aemeasurable (ae_lt_top hSumMeas hFinite)
      _ = _ := congrArg ENNReal.toReal hRateTotal
