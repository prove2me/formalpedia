-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_original_BV_signed_finite_simple_compensated_L1_zero_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:35:34.94284+00:00
-- url     : https://prove2.me/submissions/5b9380ae-5879-4943-b76e-58e87add1357

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_finite_simple_count_compensated_L1_zero_mean
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
    (Hpos Hneg : ℕ → Ω → ℝ≥0∞)
    (hHpos : ∀ i ∈ S, Measurable[𝓕 (s i)] (Hpos i))
    (hHneg : ∀ i ∈ S, Measurable[𝓕 (s i)] (Hneg i))
    (hMpos : ∀ i ∈ S, Measurable (Hpos i))
    (hMneg : ∀ i ∈ S, Measurable (Hneg i))
    (F : ℕ → (ℝ≥0 → ℝ) → ℝ≥0∞) (hF : ∀ i ∈ S, Measurable (F i))
    (N : ℕ → Ω → ℝ≥0∞)
    (hN : ∀ i ∈ S, ∀ ω : Ω, N i ω =
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ Iio (0 : ℝ)))
    (hExtract : ∀ i ∈ S, ∀ ω : Ω,
      N i ω = F i (fun v : ℝ≥0 => X.X (s i + v) ω - X.X (s i) ω))
    (Jpos Kpos Jneg Kneg : Ω → ℝ≥0∞)
    (hJpos : ∀ ω, Jpos ω = ∑ i ∈ S, Hpos i ω * N i ω)
    (hKpos : ∀ ω, Kpos ω = ∑ i ∈ S, Hpos i ω *
      (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ))))
    (hJneg : ∀ ω, Jneg ω = ∑ i ∈ S, Hneg i ω * N i ω)
    (hKneg : ∀ ω, Kneg ω = ∑ i ∈ S, Hneg i ω *
      (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ))))
    (hJposm : AEMeasurable Jpos P) (hKposm : AEMeasurable Kpos P)
    (hJnegm : AEMeasurable Jneg P) (hKnegm : AEMeasurable Kneg P)
    (hJposae : ∀ᵐ ω ∂P, Jpos ω < ⊤) (hKposae : ∀ᵐ ω ∂P, Kpos ω < ⊤)
    (hJnegae : ∀ᵐ ω ∂P, Jneg ω < ⊤) (hKnegae : ∀ᵐ ω ∂P, Kneg ω < ⊤)
    (hKposfin : (∫⁻ ω, Kpos ω ∂P) < ⊤)
    (hKnegfin : (∫⁻ ω, Kneg ω ∂P) < ⊤) :
    Integrable (fun ω =>
      ((Jpos ω).toReal - (Kpos ω).toReal) -
      ((Jneg ω).toReal - (Kneg ω).toReal)) P ∧
    (∫ ω, ((Jpos ω).toReal - (Kpos ω).toReal) -
      ((Jneg ω).toReal - (Kneg ω).toReal) ∂P) = 0 := by
  have hp :=
    avram_wave8_22_original_BV_finite_simple_count_compensated_L1_zero_mean
      X hBV hFinite S s t hst Hpos hHpos hMpos F hF N hN hExtract
      Jpos Kpos hJpos hKpos hJposm hKposm hJposae hKposae hKposfin
  have hn :=
    avram_wave8_22_original_BV_finite_simple_count_compensated_L1_zero_mean
      X hBV hFinite S s t hst Hneg hHneg hMneg F hF N hN hExtract
      Jneg Kneg hJneg hKneg hJnegm hKnegm hJnegae hKnegae hKnegfin
  exact ⟨hp.1.sub hn.1, by rw [integral_sub hp.1 hn.1, hp.2, hn.2, sub_self]⟩
