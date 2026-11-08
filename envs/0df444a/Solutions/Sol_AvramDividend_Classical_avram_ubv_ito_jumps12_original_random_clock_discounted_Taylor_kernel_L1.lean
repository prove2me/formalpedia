-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_ito_jumps12_original_random_clock_discounted_Taylor_kernel_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T14:51:54.866912+00:00
-- url     : https://prove2.me/submissions/71e3b47b-3c07-4222-bfd9-5c348544b3e4

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_stopped_Taylor_arbitrary_predictable_band_product_Integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_nnreal_stopping_inclusive_predictable_mask

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! The new clock is the actual filtration stopping time, not an independent clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0))) :
    let a : (ℝ≥0 × Ω) → ℝ := fun p =>
      if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    let GW : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * HS p
    let GWσ : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if p.1.1 ≤ σ p.1.2 then GW p else 0
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      Integrable GWσ (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  let A : Set (((ℝ≥0 × Ω) × ℝ)) :=
    {p : ℝ≥0 × Ω | p.1 ≤ σ p.2} ×ˢ Set.univ
  have hmask : MeasurableSet[𝓕.rightCont.predictable]
      {p : ℝ≥0 × Ω | p.1 ≤ σ p.2} :=
    avram_wave4_p1_nnreal_stopping_inclusive_predictable_mask
      𝓕.rightCont σ hσ
  have hAm : MeasurableSet A := by
    exact hmask.prod MeasurableSet.univ
  have hi :=
    avram_wave6_02_actual_discounted_stopped_Taylor_arbitrary_predictable_band_product_Integrable
      X x D hD w C u v δ hw hw_cont hw_neg
      hu hδ hδone huv hv q hq T μ hμ A hAm
  have hindicator (f : ((ℝ≥0 × Ω) × ℝ) → ℝ) :
      A.indicator f = fun p => if p.1.1 ≤ σ p.1.2 then f p else 0 := by
    funext p
    by_cases hp : p.1.1 ≤ σ p.1.2
    · simp [A, Set.indicator, hp]
    · simp [A, Set.indicator, hp]
  simpa only [hindicator] using hi
