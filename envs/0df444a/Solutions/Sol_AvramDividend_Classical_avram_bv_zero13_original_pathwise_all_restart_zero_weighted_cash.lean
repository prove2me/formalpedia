-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_zero13_original_pathwise_all_restart_zero_weighted_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T00:17:12.960124+00:00
-- url     : https://prove2.me/submissions/b255ddf9-c124-4dba-86c0-0c59eb5a6398

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_postpayment_zero_Ioc_cash_eq_drift
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_no_jump_interval_is_drift_only
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
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
    (H : ℝ≥0) (hH : 0 < H) :
    ∀ᵐ ω ∂P,
      ∀ (s T : ℝ≥0), s ≤ T → T ≤ H →
      (H : ℝ≥0∞) < ruinTime X x D ω →
      (∀ u : ℝ≥0, s ≤ u → u ≤ T →
        riskProcess X x D u ω -
          (rightLimit D u ω - D u ω) = 0) →
      (∀ u : ℝ≥0, u ∈ Ioc s T →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) →
      ∀ f : ℝ → ℝ≥0∞,
        (∫⁻ t in Ioc (s : ℝ) (T : ℝ), f t
          ∂(dividendMeasure D ω)) =
        (∫⁻ t in Ioc (s : ℝ) (T : ℝ), f t
          ∂((ENNReal.ofReal X.drift) • volume)) := by
  filter_upwards [avram_wave4_04a_bv_actual_no_jump_interval_is_drift_only
    X hBV hFinite H hH] with ω hsource
  intro s T hsT hTH hsurv hpostzero hnoj f
  let μ : Measure ℝ := dividendMeasure D ω
  let ν : Measure ℝ := (ENNReal.ofReal X.drift) • volume
  have hCash (a b : ℝ) (ha0 : 0 ≤ a) (hsa : (s : ℝ) ≤ a)
      (hab : a ≤ b) (hb : b ≤ (T : ℝ)) :
      (dividendMeasure D ω) (Ioc a b) =
        ENNReal.ofReal (X.drift * (b - a)) := by
    let aa : ℝ≥0 := ⟨a, ha0⟩
    let bb : ℝ≥0 := ⟨b, le_trans ha0 hab⟩
    have hAB : aa ≤ bb := hab
    have hSB : s ≤ aa := hsa
    have hBT : bb ≤ T := hb
    have hlocal : ∀ u : ℝ≥0, u ∈ Ioc aa bb →
        X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u = 0 := by
      intro u hu
      exact hnoj u ⟨lt_of_le_of_lt hSB hu.1, le_trans hu.2 hBT⟩
    have hline : X.X bb ω - X.X aa ω =
        X.drift * ((bb : ℝ) - (aa : ℝ)) := by
      nlinarith [hsource aa bb hAB (le_trans hBT hTH) hlocal]
    have hcashNN :=
      avram_bv_zero13_original_postpayment_zero_Ioc_cash_eq_drift
        X hBV hFinite x C D hD ω aa bb hAB
        (hpostzero aa hSB (le_trans hAB hBT))
        (hpostzero bb (le_trans hSB hAB) hBT) hline
    change (dividendMeasure D ω) (Ioc a b) =
      ENNReal.ofReal (X.drift * (b - a)) at hcashNN
    exact hcashNN
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := s.property
  have hFiniteCash : μ (Ioc (s : ℝ) (T : ℝ)) < ⊤ := by
    change (dividendMeasure D ω) (Ioc (s : ℝ) (T : ℝ)) < ⊤
    rw [hCash (s : ℝ) (T : ℝ) hs0 le_rfl hsT le_rfl]
    exact ENNReal.ofReal_lt_top
  have hMass (a b : ℝ) (ha0 : 0 ≤ a) (hsa : (s : ℝ) ≤ a)
      (hab : a ≤ b) (hb : b ≤ (T : ℝ)) : μ (Ioc a b) = ν (Ioc a b) := by
    change (dividendMeasure D ω) (Ioc a b) =
      ((ENNReal.ofReal X.drift) • volume) (Ioc a b)
    rw [hCash a b ha0 hsa hab hb]
    simpa [Measure.smul_apply, Real.volume_Ioc, smul_eq_mul] using
      (ENNReal.ofReal_mul hDrift :
        ENNReal.ofReal (X.drift * (b - a)) =
          ENNReal.ofReal X.drift * ENNReal.ofReal (b - a))
  have hMassST : μ (Ioc (s : ℝ) (T : ℝ)) =
      ν (Ioc (s : ℝ) (T : ℝ)) :=
    hMass (s : ℝ) (T : ℝ) hs0 le_rfl hsT le_rfl
  have heq : μ.restrict (Ioc (s : ℝ) (T : ℝ)) =
      ν.restrict (Ioc (s : ℝ) (T : ℝ)) := by
    letI : IsFiniteMeasure (μ.restrict (Ioc (s : ℝ) (T : ℝ))) := by
      refine ⟨?_⟩
      simpa using hFiniteCash
    apply Measure.ext_of_Ioc_finite
      (μ.restrict (Ioc (s : ℝ) (T : ℝ)))
      (ν.restrict (Ioc (s : ℝ) (T : ℝ)))
    · simpa using hMassST
    · intro a b hab
      have hinter :
          Ioc a b ∩ Ioc (s : ℝ) (T : ℝ) =
            Ioc (max a (s : ℝ)) (min b (T : ℝ)) := by
        ext z
        simp [lt_min_iff, max_lt_iff, and_comm, and_left_comm, and_assoc]
      have hlocal : μ (Ioc (max a (s : ℝ)) (min b (T : ℝ))) =
          ν (Ioc (max a (s : ℝ)) (min b (T : ℝ))) := by
        by_cases hbound : max a (s : ℝ) ≤ min b (T : ℝ)
        · exact hMass _ _
            (le_trans hs0 (le_max_right _ _))
            (le_max_right _ _) hbound (min_le_right _ _)
        · have hEmpty : Ioc (max a (s : ℝ)) (min b (T : ℝ)) = ∅ :=
            Set.Ioc_eq_empty (fun hlt => hbound (le_of_lt hlt))
          simp [hEmpty]
      simpa [Measure.restrict_apply, hinter] using hlocal
  exact congrArg (fun m : Measure ℝ => ∫⁻ t, f t ∂m) heq