-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_countable_signed_predictable_l1_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:27:00.373461+00:00
-- url     : https://prove2.me/submissions/aeb5cdc2-f1b9-46a7-91eb-4a2567bb8cec

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_countable_predictable_weighted_rate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Signed countable predictable-simple original marked counts are real L¹
when each of the positive and negative prescribed total rates is finite. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℕ → ℝ≥0) (hst : ∀ i, s i ≤ t i)
    (B : ℕ → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (Wpos Wneg : ℕ → Ω → ℝ≥0∞)
    (hWp : ∀ i, Measurable[𝓕 (s i)] (Wpos i))
    (hWn : ∀ i, Measurable[𝓕 (s i)] (Wneg i))
    (hRate : ∀ i, (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i) ∂P) = (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)))
    (hSumPos : (∑' i, (∫⁻ ω, Wpos i ω ∂P) * (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))) < ⊤)
    (hSumNeg : (∑' i, (∫⁻ ω, Wneg i ω ∂P) * (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))) < ⊤) :
    let pos : Ω → ℝ≥0∞ := fun ω => ∑' i, Wpos i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i)
    let neg : Ω → ℝ≥0∞ := fun ω => ∑' i, Wneg i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i)
    let rp : ℝ≥0∞ := ∑' i, (∫⁻ ω, Wpos i ω ∂P) * (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))
    let rn : ℝ≥0∞ := ∑' i, (∫⁻ ω, Wneg i ω ∂P) * (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))
    Integrable (fun ω => (pos ω).toReal - (neg ω).toReal) P ∧
      (∫ ω, (pos ω).toReal - (neg ω).toReal ∂P) = rp.toReal - rn.toReal := by
  dsimp only
  have hMp (i : ℕ) : Measurable (fun ω : Ω => Wpos i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i)) :=
    ((hWp i).mono (𝓕.le (s i)) le_rfl).mul
      (avram_p2_e_compensator_intrinsic_rectangle_count_measurable
        X (s i) (t i) (hst i) (B i) (hB i))
  have hMn (i : ℕ) : Measurable (fun ω : Ω => Wneg i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i)) :=
    ((hWn i).mono (𝓕.le (s i)) le_rfl).mul
      (avram_p2_e_compensator_intrinsic_rectangle_count_measurable
        X (s i) (t i) (hst i) (B i) (hB i))
  have hSumMp : Measurable (fun ω : Ω => ∑' i, Wpos i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i)) :=
    Measurable.tsum hMp
  have hSumMn : Measurable (fun ω : Ω => ∑' i, Wneg i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i)) :=
    Measurable.tsum hMn
  have hLpos := avram_p2_e_compensator_countable_predictable_weighted_rate
    X s t hst B hB Wpos hWp hRate
  have hLneg := avram_p2_e_compensator_countable_predictable_weighted_rate
    X s t hst B hB Wneg hWn hRate
  have hFp : (∫⁻ ω, ∑' i, Wpos i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i) ∂P) ≠ ⊤ := by
    rw [hLpos]
    exact ne_of_lt hSumPos
  have hFn : (∫⁻ ω, ∑' i, Wneg i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i) ∂P) ≠ ⊤ := by
    rw [hLneg]
    exact ne_of_lt hSumNeg
  have hIp := integrable_toReal_of_lintegral_ne_top hSumMp.aemeasurable hFp
  have hIn := integrable_toReal_of_lintegral_ne_top hSumMn.aemeasurable hFn
  have hMeanP : (∫ ω, (∑' i, Wpos i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i)).toReal ∂P) =
      (∑' i, (∫⁻ ω, Wpos i ω ∂P) * (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))).toReal := by
    calc
      _ = (∫⁻ ω, ∑' i, Wpos i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i) ∂P).toReal :=
        integral_toReal hSumMp.aemeasurable (ae_lt_top hSumMp hFp)
      _ = _ := congrArg ENNReal.toReal hLpos
  have hMeanN : (∫ ω, (∑' i, Wneg i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i)).toReal ∂P) =
      (∑' i, (∫⁻ ω, Wneg i ω ∂P) * (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))).toReal := by
    calc
      _ = (∫⁻ ω, ∑' i, Wneg i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i) ∂P).toReal :=
        integral_toReal hSumMn.aemeasurable (ae_lt_top hSumMn hFn)
      _ = _ := congrArg ENNReal.toReal hLneg
  constructor
  · exact hIp.sub hIn
  · calc
      (∫ ω, (∑' i, Wpos i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i)).toReal -
        (∑' i, Wneg i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i)).toReal ∂P) =
        (∫ ω, (∑' i, Wpos i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i)).toReal ∂P) -
        (∫ ω, (∑' i, Wneg i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i)).toReal ∂P) :=
          integral_sub hIp hIn
      _ = _ := by rw [hMeanP, hMeanN]
