-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_true_clock_physical_integral_DCT
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:56:24.505455+00:00
-- url     : https://prove2.me/submissions/d801d615-837f-42eb-bb09-679654a6b5e6

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_true_clock_eventually_strict_preruin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Source stopped physical-time integrals converge under true global L¹ domination. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (μ : Measure ℝ≥0) (f : ℝ≥0 → ℝ)
    (hf : Integrable f μ) :
    Tendsto
      (fun n : ℕ => ∫ t : ℝ≥0,
        ({s : ℝ≥0 | (s : ℝ≥0∞) <
          min (ruinTime X x D ω) (n : ℝ≥0∞)}).indicator f t ∂μ)
      atTop
      (nhds (∫ t : ℝ≥0,
        ({s : ℝ≥0 | (s : ℝ≥0∞) < ruinTime X x D ω}).indicator f t ∂μ)) := by
  let S : ℕ → Set ℝ≥0 := fun n =>
    {t | (t : ℝ≥0∞) < min (ruinTime X x D ω) (n : ℝ≥0∞)}
  let Sfull : Set ℝ≥0 :=
    {t | (t : ℝ≥0∞) < ruinTime X x D ω}
  have hs : ∀ n : ℕ, MeasurableSet (S n) := by
    intro n
    dsimp [S]
    measurability
  have hi : ∀ n : ℕ, Integrable ((S n).indicator f) μ :=
    fun n => hf.indicator (hs n)
  have hb : ∀ n : ℕ, ∀ᵐ t : ℝ≥0 ∂μ,
      ‖(S n).indicator f t‖ ≤ ‖f t‖ := by
    intro n
    apply Filter.Eventually.of_forall
    intro t
    by_cases ht : t ∈ S n
    · simp [ht]
    · simp [ht]
  have hl : ∀ᵐ t : ℝ≥0 ∂μ,
      Tendsto (fun n : ℕ => (S n).indicator f t)
        atTop (nhds (Sfull.indicator f t)) := by
    apply Filter.Eventually.of_forall
    intro t
    have heq : (fun n : ℕ => (S n).indicator f t) =ᶠ[atTop]
        (fun _ => Sfull.indicator f t) := by
      by_cases hr : (t : ℝ≥0∞) < ruinTime X x D ω
      · have hEventually :=
          avram_p4_e_localise_original_true_clock_eventually_strict_preruin
            X x C D hD ω t hr
        filter_upwards [hEventually] with n hn
        have ht1 : t ∈ S n := hn
        have ht2 : t ∈ Sfull := hr
        simp [Set.indicator, ht1, ht2]
      · apply Filter.Eventually.of_forall
        intro n
        have ht1 : t ∉ S n := by
          intro h
          exact hr (lt_of_lt_of_le h (min_le_left _ _))
        have ht2 : t ∉ Sfull := hr
        simp [Set.indicator, ht1, ht2]
    exact (Filter.tendsto_congr' heq).2 tendsto_const_nhds
  exact tendsto_integral_of_dominated_convergence
    (fun t : ℝ≥0 => ‖f t‖)
    (fun n => (hi n).aestronglyMeasurable)
    hf.norm hb hl
