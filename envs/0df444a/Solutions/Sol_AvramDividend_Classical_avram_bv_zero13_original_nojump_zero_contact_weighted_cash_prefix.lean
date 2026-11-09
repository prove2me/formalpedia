-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_zero13_original_nojump_zero_contact_weighted_cash_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T23:05:06.949044+00:00
-- url     : https://prove2.me/submissions/e5d29770-5063-443f-bfdb-0f0edf0549ac

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_active_zero_contact_Ioc_cash_eq_drift
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_no_jump_interval_is_drift_only
import Theorems.Thm_AvramDividend_Classical_measure_restrict_Ioc_eq_of_local_Ioc_agreement
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hDrift : 0 ≤ X.drift)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P,
      (T : ℝ≥0∞) < ruinTime X x D ω →
      (∀ u : ℝ≥0, u ≤ T → riskProcess X x D u ω = 0) →
      (∀ u : ℝ≥0, u ∈ Ioc (0 : ℝ≥0) T →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) →
      ∀ f : ℝ → ℝ≥0∞,
        (∫⁻ t in Ioc (0 : ℝ) (T : ℝ), f t
          ∂(dividendMeasure D ω)) =
        (∫⁻ t in Ioc (0 : ℝ) (T : ℝ), f t
          ∂((ENNReal.ofReal X.drift) • volume)) := by
  filter_upwards [avram_wave4_04a_bv_actual_no_jump_interval_is_drift_only
    X hBV hFinite T hT] with ω hsource
  intro hsurv hzero hnoj f
  let μ : Measure ℝ := dividendMeasure D ω
  let ν : Measure ℝ := (ENNReal.ofReal X.drift) • volume
  have hactive (u : ℝ≥0) (hu : u ≤ T) :
      u = 0 ∨ (u : ℝ≥0∞) < ruinTime X x D ω := by
    right
    exact lt_of_le_of_lt (by exact_mod_cast hu) hsurv
  have hCash (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t)
      (ht : t ≤ (T : ℝ)) :
      (dividendMeasure D ω) (Ioc s t) =
        ENNReal.ofReal (X.drift * (t - s)) := by
    let ss : ℝ≥0 := ⟨s, hs⟩
    let tt : ℝ≥0 := ⟨t, le_trans hs hst⟩
    have hstNN : ss ≤ tt := hst
    have htNN : tt ≤ T := ht
    have hlocal : ∀ u : ℝ≥0, u ∈ Ioc ss tt →
        X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u = 0 := by
      intro u hu
      exact hnoj u ⟨lt_of_le_of_lt (show (0 : ℝ≥0) ≤ ss from zero_le) hu.1,
        le_trans hu.2 htNN⟩
    have hline : X.X tt ω - X.X ss ω =
        X.drift * ((tt : ℝ) - (ss : ℝ)) := by
      nlinarith [hsource ss tt hstNN htNN hlocal]
    have hcashNN :=
      avram_bv_zero13_original_active_zero_contact_Ioc_cash_eq_drift
        X hBV hFinite x C D hD ω ss tt hstNN
        (hactive ss (le_trans hstNN htNN))
        (hactive tt htNN) (hzero ss (le_trans hstNN htNN))
        (hzero tt htNN) hline
    change (dividendMeasure D ω) (Ioc s t) =
        ENNReal.ofReal (X.drift * (t - s)) at hcashNN
    exact hcashNN
  have hFiniteCash : μ (Ioc (0 : ℝ) (T : ℝ)) < ⊤ := by
    change (dividendMeasure D ω) (Ioc (0 : ℝ) (T : ℝ)) < ⊤
    rw [hCash 0 (T : ℝ) (le_refl _)
      (by exact_mod_cast (show (0 : ℝ≥0) ≤ T from zero_le)) le_rfl]
    exact ENNReal.ofReal_lt_top
  have hMass (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t)
      (ht : t ≤ (T : ℝ)) : μ (Ioc s t) = ν (Ioc s t) := by
    change (dividendMeasure D ω) (Ioc s t) =
      ((ENNReal.ofReal X.drift) • volume) (Ioc s t)
    rw [hCash s t hs hst ht]
    simpa [Measure.smul_apply, Real.volume_Ioc, smul_eq_mul] using
      (ENNReal.ofReal_mul hDrift :
        ENNReal.ofReal (X.drift * (t - s)) =
          ENNReal.ofReal X.drift * ENNReal.ofReal (t - s))
  have heq : μ.restrict (Ioc (0 : ℝ) (T : ℝ)) =
      ν.restrict (Ioc (0 : ℝ) (T : ℝ)) :=
    measure_restrict_Ioc_eq_of_local_Ioc_agreement
      μ ν (T : ℝ)
      (by exact_mod_cast (show (0 : ℝ≥0) ≤ T from zero_le))
      hFiniteCash hMass
  exact congrArg (fun m : Measure ℝ => ∫⁻ t, f t ∂m) heq
