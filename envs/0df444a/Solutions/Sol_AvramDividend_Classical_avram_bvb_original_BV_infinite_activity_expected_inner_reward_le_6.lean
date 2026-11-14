-- Prove2me | solution 6 for AvramDividend.Classical.avram_bvb_original_BV_infinite_activity_expected_inner_reward_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:42:55.613803+00:00
-- url     : https://prove2.me/submissions/a5a22a28-2e99-44d4-a82b-50161b61a4cd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva33_original_BV_infinite_activity_inner_cash_terminal_integrable
import Theorems.Thm_AvramDividend_Classical_avram_bva34_original_infinite_activity_physical_L1_error_jump_drift_source
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 < T)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    ∀ n : ℕ, (∫ ω, F n ω ∂P) ≤ w x := by
  intro δ S F n
  letI : IsProbabilityMeasure P := X.isProbability
  have hFI : Integrable (F n) P := by
    simpa only [F, δ, S] using
      (avram_bva33_original_BV_infinite_activity_inner_cash_terminal_integrable
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
        hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT hInfinite n)
  have hBound (ε : ℝ) (hε : 0 < ε) :
      (∫ ω, F n ω ∂P) ≤ w x + ε := by
    obtain ⟨J, B, R, hJI, hBI, hRI, hJ0, hB0, hRnonneg, hRmean, hpath⟩ :=
      avram_bva34_original_infinite_activity_physical_L1_error_jump_drift_source
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
        hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT hInfinite n ε hε
    have hJB : Integrable (fun ω => J ω + B ω) P := hJI.add hBI
    have hWB : Integrable (fun ω => w x + (J ω + B ω)) P :=
      (integrable_const (w x)).add hJB
    have hRight : Integrable (fun ω => w x + (J ω + B ω) + R ω) P :=
      hWB.add hRI
    have hLe := integral_mono_ae hFI hRight hpath
    have hEval :
        (∫ ω, w x + (J ω + B ω) + R ω ∂P) =
          w x + ((∫ ω, J ω ∂P) + (∫ ω, B ω ∂P)) +
            (∫ ω, R ω ∂P) := by
      rw [integral_add hWB hRI]
      rw [integral_add (integrable_const (w x)) hJB]
      rw [integral_add hJI hBI]
      simp
    rw [hEval, hJ0] at hLe
    linarith
  by_contra hfail
  have hgt : w x < (∫ ω, F n ω ∂P) := lt_of_not_ge hfail
  have hpos : 0 < ((∫ ω, F n ω ∂P) - w x) / 2 := by linarith
  have hs := hBound (((∫ ω, F n ω ∂P) - w x) / 2) hpos
  linarith
