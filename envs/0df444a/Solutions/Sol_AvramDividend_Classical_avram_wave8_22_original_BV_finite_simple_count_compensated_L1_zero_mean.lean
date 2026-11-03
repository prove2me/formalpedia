-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_original_BV_finite_simple_count_compensated_L1_zero_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:28:31.410008+00:00
-- url     : https://prove2.me/submissions/a5dbf143-9573-4d20-abc9-47340bde0c2b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_finite_simple_predictable_compensation_of_extractors
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (S : Finset ℕ) (s t : ℕ → ℝ≥0) (hst : ∀ i ∈ S, s i ≤ t i)
    (H : ℕ → Ω → ℝ≥0∞)
    (hH : ∀ i ∈ S, Measurable[𝓕 (s i)] (H i))
    (hHm : ∀ i ∈ S, Measurable (H i))
    (F : ℕ → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hF : ∀ i ∈ S, Measurable (F i))
    (N : ℕ → Ω → ℝ≥0∞)
    (hN : ∀ i ∈ S, ∀ ω : Ω, N i ω =
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ Iio (0 : ℝ)))
    (hExtract : ∀ i ∈ S, ∀ ω : Ω,
      N i ω = F i (fun v : ℝ≥0 => X.X (s i + v) ω - X.X (s i) ω))
    (J K : Ω → ℝ≥0∞)
    (hJ : ∀ ω, J ω = ∑ i ∈ S, H i ω * N i ω)
    (hK : ∀ ω, K ω = ∑ i ∈ S, H i ω *
      (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ))))
    (hJm : AEMeasurable J P) (hKm : AEMeasurable K P)
    (hJae : ∀ᵐ ω ∂P, J ω < ⊤) (hKae : ∀ᵐ ω ∂P, K ω < ⊤)
    (hKfin : (∫⁻ ω, K ω ∂P) < ⊤) :
    Integrable (fun ω => (J ω).toReal - (K ω).toReal) P ∧
    (∫ ω, (J ω).toReal - (K ω).toReal ∂P) = 0 := by
  have hComp :=
    avram_wave7_01_bv_finite_simple_predictable_compensation_of_extractors
      X hBV hFinite S s t hst H hH F hF
      (by intro i hi ω; exact (hN i hi ω).symm.trans (hExtract i hi ω))
  have hKlaw :
      (∫⁻ ω, K ω ∂P) =
      ∑ i ∈ S, (∫⁻ ω, H i ω ∂P) *
        ((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by
    calc
      _ = ∫⁻ ω, ∑ i ∈ S, H i ω *
          (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ))) ∂P := by
            apply lintegral_congr; intro ω; exact hK ω
      _ = ∑ i ∈ S, ∫⁻ ω, H i ω *
          (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ))) ∂P := by
            rw [lintegral_finset_sum S]
            intro i hi; exact (hHm i hi).mul_const _
      _ = _ := by
        apply Finset.sum_congr rfl; intro i hi
        rw [lintegral_mul_const _ (hHm i hi)]
        simp only [mul_assoc]
  have hEN : (∫⁻ ω, J ω ∂P) = (∫⁻ ω, K ω ∂P) := by
    calc
      _ = ∫⁻ ω, ∑ i ∈ S, H i ω *
          ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc (s i) (t i) ×ˢ Iio (0 : ℝ)) ∂P := by
              apply lintegral_congr; intro ω; rw [hJ ω]
              apply Finset.sum_congr rfl; intro i hi; rw [hN i hi ω]
      _ = _ := hComp
      _ = _ := hKlaw.symm
  have hJfin : (∫⁻ ω, J ω ∂P) < ⊤ := by rw [hEN]; exact hKfin
  have hJne : ∀ᵐ ω ∂P, J ω ≠ ⊤ := hJae.mono (fun ω hω => ne_of_lt hω)
  have hKne : ∀ᵐ ω ∂P, K ω ≠ ⊤ := hKae.mono (fun ω hω => ne_of_lt hω)
  have hJI : Integrable (fun ω => (J ω).toReal) P :=
    (integrable_toReal_iff hJm hJne).2 (ne_of_lt hJfin)
  have hKI : Integrable (fun ω => (K ω).toReal) P :=
    (integrable_toReal_iff hKm hKne).2 (ne_of_lt hKfin)
  have hE : (∫ ω, (J ω).toReal ∂P) = (∫ ω, (K ω).toReal ∂P) := by
    rw [integral_toReal hJm hJae, integral_toReal hKm hKae, hEN]
  exact ⟨hJI.sub hKI, by rw [integral_sub hJI hKI, hE, sub_self]⟩
