-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_phys16_original_firstjump_straddling_masked_strict_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T14:11:38.073419+00:00
-- url     : https://prove2.me/submissions/1aa8ccb7-fe9c-4d2c-88b7-78752369a744

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_strict_prejump_zero_cash_of_first_source_jump
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Payment-clock masking removes the first negative source jump atom from
    the zero-contact half-open cell and keeps strictly earlier drift cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) (hDrift : 0 ≤ X.drift)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ≥0) (hH : 0 < H) :
    ∀ᵐ ω ∂P, ∀ (s J : ℝ≥0), s < J → J ≤ H →
      (J : WithTop ℝ≥0) ≤
        (⨅ u : ℝ≥0,
          if 0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0
          then (u : WithTop ℝ≥0) else ⊤) →
      ∀ (a : ℕ → ℝ≥0),
      (∀ n, s ≤ a n ∧ a n < J) →
      Monotone (fun n : ℕ => Ioc (s : ℝ) ((a n : ℝ≥0) : ℝ)) →
      (⋃ n, Ioc (s : ℝ) ((a n : ℝ≥0) : ℝ)) =
        Ioo (s : ℝ) (J : ℝ) →
      (∀ u : ℝ≥0, s ≤ u → u < J →
        riskProcess X x D u ω -
          (rightLimit D u ω - D u ω) = 0) →
      ∀ f : ℝ → ℝ≥0∞, Measurable f →
      (∫⁻ t in paymentTimes (J : ℝ≥0∞) ∩
          Ioc (s : ℝ) (J : ℝ), f t
        ∂(dividendMeasure D ω)) =
      (∫⁻ t in Ioo (s : ℝ) (J : ℝ), f t
        ∂((ENNReal.ofReal X.drift) • volume)) := by
  filter_upwards [
    avram_bv_zero13_original_strict_prejump_zero_cash_of_first_source_jump
      X hBV hFinite hDrift x C D hD H hH
  ] with ω hω
  intro s J hsj hJH hBefore a ha hMono hCover hZero f hf
  have hMask :
      paymentTimes (J : ℝ≥0∞) ∩ Ioc (s : ℝ) (J : ℝ) =
        Ioo (s : ℝ) (J : ℝ) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioo]
    change
      (0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < (J : ℝ≥0∞))) ∧
        (s : ℝ) < t ∧ t ≤ (J : ℝ) ↔
        (s : ℝ) < t ∧ t < (J : ℝ)
    constructor
    · rintro ⟨⟨htnonneg, htZeroOr⟩, hst, htJ⟩
      have htpos : 0 < t :=
        lt_of_le_of_lt (by exact_mod_cast s.property) hst
      rcases htZeroOr with ht0 | htlt
      · exact False.elim ((ne_of_gt htpos) ht0)
      · exact ⟨hst,
          (ENNReal.ofReal_lt_coe_iff (le_of_lt htpos)).mp htlt⟩
    · rintro ⟨hst, htlt⟩
      have htpos : 0 < t :=
        lt_of_le_of_lt (by exact_mod_cast s.property) hst
      refine ⟨⟨le_of_lt htpos, Or.inr ?_⟩, hst, le_of_lt htlt⟩
      exact (ENNReal.ofReal_lt_coe_iff (le_of_lt htpos)).mpr htlt
  calc
    (∫⁻ t in paymentTimes (J : ℝ≥0∞) ∩
        Ioc (s : ℝ) (J : ℝ), f t
      ∂(dividendMeasure D ω)) =
      (∫⁻ t in Ioo (s : ℝ) (J : ℝ), f t
        ∂(dividendMeasure D ω)) := by rw [hMask]
    _ = _ := hω s J hsj hJH hBefore a ha hMono hCover hZero f hf
