-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_02_actual_discounted_stopped_Taylor_exists_finite_predictable_marked_signed_compensator_L1_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T08:27:22.773846+00:00
-- url     : https://prove2.me/submissions/92b96b71-4305-4d39-9307-77177045a6c0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_stopped_Taylor_exists_finite_physical_predictable_band_with_small_L1_tail
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_Taylor_physical_signed_compensator_cutoff_error_le_eLpNorm_one_tail
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
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
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      ∀ (ε : ℝ≥0∞) (hε : ε ≠ 0),
      ∃ A : Set (((ℝ≥0 × Ω) × ℝ)),
        MeasurableSet A ∧
        (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) A < ⊤ ∧
        |(∫ p, A.indicator GW p
            ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) -
          (∫ p, GW p
            ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ)))))| ≤
          (eLpNorm (Aᶜ.indicator GW) (1 : ℝ≥0∞)
            (μ.prod (X.ν.restrict (Iio (0 : ℝ))))).toReal ∧
        eLpNorm (Aᶜ.indicator GW) (1 : ℝ≥0∞)
          (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) < ε) := by
  classical
  intro a Y H HS GW
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  intro ε hε
  let mprod : Measure ((ℝ≥0 × Ω) × ℝ) :=
    μ.prod (X.ν.restrict (Iio (0 : ℝ)))
  obtain ⟨A, hAm, hAf, hTail⟩ :=
    avram_wave6_02_actual_discounted_stopped_Taylor_exists_finite_physical_predictable_band_with_small_L1_tail
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv q hq T μ hμ ε hε
  refine ⟨A, hAm, hAf, ?_, hTail⟩
  exact
    avram_wave6_02_actual_discounted_Taylor_physical_signed_compensator_cutoff_error_le_eLpNorm_one_tail
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv q hq T μ hμ A hAm
