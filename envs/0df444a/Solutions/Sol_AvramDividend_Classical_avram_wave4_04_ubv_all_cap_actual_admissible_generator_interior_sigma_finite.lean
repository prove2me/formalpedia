-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04_ubv_all_cap_actual_admissible_generator_interior_sigma_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:52:38.038159+00:00
-- url     : https://prove2.me/submissions/958aa609-c02b-4f75-8345-46ee2e197fdb

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_same_source_sigma_finite_cap_occupation
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_same_source_positive_preruin_sigma_finite_occupation
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_allCap_admissible_initial_capital_nonneg
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original, jointly adapted controlled reserve lies strictly inside
the actual extended-real cap for a.e. deterministic-time observation
before ruin, including the infinite-cap case. This does not constrain
the path-dependent Stieltjes dividend measure at boundary contact. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC0 : C ≠ 0)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, horizons n ≤ ε)
    (μ : Measure ℝ≥0) [SFinite μ] :
    ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω) →
      0 < riskProcess X x D t ω ∧
        ENNReal.ofReal (riskProcess X x D t ω) < C := by
  have hx : 0 ≤ x :=
    avram_wave3_04_allCap_admissible_initial_capital_nonneg
      X x C hxc D hD
  have hPre (ω : Ω) (s : ℝ≥0)
      (hs : (s : ℝ≥0∞) < ruinTime X x D ω) :=
    capped_riskProcess_range_before_ruin_including_zero
      X x hx C hxc D hD ω s hs
  have hLower :=
    avram_wave4_04_ubv_same_source_positive_preruin_sigma_finite_occupation
      X hBV x D hD.1.1 (fun ω s hs => (hPre ω s hs).1)
      times horizons hdense hpos hcofinal μ
  have hUpper : ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω) →
        ENNReal.ofReal (riskProcess X x D t ω) < C := by
    by_cases hTop : C = ⊤
    · filter_upwards [] with ω
      filter_upwards [] with t
      intro ht
      simp [hTop]
    · have hc : 0 ≤ C.toReal := ENNReal.toReal_nonneg
      have hC : ENNReal.ofReal C.toReal = C :=
        ENNReal.ofReal_toReal hTop
      have hUpperFin :=
        avram_wave4_04_ubv_same_source_sigma_finite_cap_occupation
          X hBV x C.toReal D hD.1.1 μ
          (fun ω s hs =>
            (ENNReal.ofReal_le_ofReal_iff hc).mp
              (show ENNReal.ofReal (riskProcess X x D s ω) ≤
                  ENNReal.ofReal C.toReal by
                simpa only [hC] using (hPre ω s hs).2))
      filter_upwards [hUpperFin] with ω hω
      filter_upwards [hω] with t ht
      intro hpre
      have hr := ht hpre
      have hnonneg := (hPre ω t hpre.2).1
      have hlt : ENNReal.ofReal (riskProcess X x D t ω) <
          ENNReal.ofReal C.toReal :=
        (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt hnonneg hr)).mpr hr
      simpa only [hC] using hlt
  filter_upwards [hLower, hUpper] with ω hLow hUp
  filter_upwards [hLow, hUp] with t htLow htUp
  intro ht
  exact ⟨htLow ht.2, htUp ht⟩
