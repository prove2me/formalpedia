-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_zero13_original_strict_prejump_zero_cash_of_first_source_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T11:42:40.284211+00:00
-- url     : https://prove2.me/submissions/f395c521-5645-4f06-89d2-249c04008fff

import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_before_first_negative_jump_source_increments_zero
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_strict_open_endpoint_zero_cash_of_prefix_cover

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- Strict zero-reserve cash before the first genuine negative original jump. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hDrift : 0 ≤ X.drift)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ≥0) (hH : 0 < H) :
    ∀ᵐ ω ∂P,
      ∀ (s J : ℝ≥0), s < J → J ≤ H →
      (J : WithTop ℝ≥0) ≤
        (⨅ u : ℝ≥0,
          if 0 < u ∧
              X.X u ω -
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
      (∫⁻ t in Ioo (s : ℝ) (J : ℝ), f t
        ∂(dividendMeasure D ω)) =
      (∫⁻ t in Ioo (s : ℝ) (J : ℝ), f t
        ∂((ENNReal.ofReal X.drift) • volume)) := by
  filter_upwards [
    avram_bv_zero13_original_strict_open_endpoint_zero_cash_of_prefix_cover
      X hBV hFinite hDrift x C D hD H hH] with ω hω
  intro s J hsJ hJH hJFirst a ha hmono hcover hzero f hf
  have hNoSource : ∀ u : ℝ≥0, u ∈ Ioo s J →
      X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 := by
    intro u hu
    have huPos : 0 < u := lt_of_le_of_lt zero_le hu.1
    have huFirst :
        (u : WithTop ℝ≥0) <
          (⨅ v : ℝ≥0,
            if 0 < v ∧
                X.X v ω -
                  Function.leftLim (fun z : ℝ≥0 => X.X z ω) v < 0
            then (v : WithTop ℝ≥0) else ⊤) :=
      lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hu.2) hJFirst
    exact avram_bv_zero13_original_before_first_negative_jump_source_increments_zero
      X ω u huPos huFirst
  exact hω s J hsJ hJH a ha hmono hcover hzero hNoSource f hf
