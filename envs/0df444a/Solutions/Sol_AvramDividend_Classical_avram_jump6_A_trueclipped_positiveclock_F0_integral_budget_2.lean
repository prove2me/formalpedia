-- Prove2me | solution 2 for AvramDividend.Classical.avram_jump6_A_trueclipped_positiveclock_F0_integral_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:06:29.903177+00:00
-- url     : https://prove2.me/submissions/bce9de7c-582b-46d7-9eee-e6c1d4d8cef5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin36_original_finitecap_any_stopped_full_reward_L1
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_predictable_grid_two_noise_initial_positive_event_zero
import Theorems.Thm_AvramDividend_Classical_avram_ja20261118_positive_clock_finite_mixed_mesh_L1_budget
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_positive_clock_event_is_initial_filtration_measurable
import Theorems.Thm_AvramDividend_Classical_avram_b22_initial_event_finite_mesh_vanishing_error_budget
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_integrable_error_global_L1_controls_initial_event_signed_integral

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w
    {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
    X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
    (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0),
    (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤
    w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (ρ : Ω → ℝ≥0) (hρstop : IsStoppingTime 𝓕.rightCont
    (fun ω => (ρ ω : WithTop ℝ≥0))) (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0)) (hρclip : ∀ ω, ρ ω ≤
    (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hCfinite : C ≠ ⊤) (κ : ℕ → Ω → ℝ≥0) (hκexact : ∀ k ω, κ k ω = (min (ρ ω : ℝ≥0∞)
    (twoSidedExitUpTime X ((k : ℝ) + 1) ω)).toNNReal) (hκstop : ∀ k, IsStoppingTime 𝓕.rightCont
    (fun ω => (κ k ω : WithTop ℝ≥0))) (H : ℕ → Ω → ℝ) (hHsource : ∀ k ω, H k ω =
    Real.exp (-(q * (κ k ω : ℝ))) * w (if κ k ω = 0 ∨ (κ k ω : ℝ≥0∞) < ruinTime X x D ω then
    x + X.X (κ k ω) ω - rightLimit D (κ k ω) ω else riskProcess X x D (κ k ω) ω) +
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ k ω : ℝ),
    ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) : ∀ (k : ℕ) (A : Set Ω),
    MeasurableSet[𝓕.rightCont 0] A → (∫ ω in A ∩ {η : Ω | κ k η ≠ 0}, H k ω ∂P) ≤
    w x * (P (A ∩ {η : Ω | κ k η ≠ 0})).toReal:= by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro k A hA
  have hKle : ∀ ω, κ k ω ≤ ρ ω := by
    intro ω
    rw [hκexact k ω]
    have hmin :
        (min (ρ ω : ℝ≥0∞) (twoSidedExitUpTime X ((k : ℝ) + 1) ω)).toNNReal
          ≤ (ρ ω : ℝ≥0∞).toNNReal :=
      ENNReal.toNNReal_mono (by simp) (min_le_left _ _)
    simpa only [ENNReal.toNNReal_coe] using hmin
  have hKbound : ∀ ω, κ k ω ≤ (n : ℝ≥0) :=
    fun ω => (hKle ω).trans (hρbound ω)
  have hHI : Integrable (H k) P :=
    avram_mix_fin36_original_finitecap_any_stopped_full_reward_L1
      X x q (le_of_lt hq) w hw_cont hw_neg C hCfinite hxc
      D hD n (κ k) (hκstop k) hKbound (H k) (hHsource k)
  obtain ⟨R, Jsmall, hRsource, hJsource, hGrids⟩ :=
    avram_jump6_A_original_predictable_grid_two_noise_initial_positive_event_zero
      X hX hFiniteActivity
  obtain ⟨G, J, Err, hGI, hJI, hEI, hGCauchy,
      hJCauchy, hESmall, hStructures, hUpper, hZeroAtStop⟩ :=
    avram_ja20261118_positive_clock_finite_mixed_mesh_L1_budget
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn (κ k) (hκstop k) hKbound (H k) (hHsource k)
      hHI hFiniteActivity R Jsmall hRsource hJsource
  have hPositive : MeasurableSet[𝓕.rightCont 0]
      {η : Ω | κ k η ≠ 0} :=
    avram_jump6_A_original_positive_clock_event_is_initial_filtration_measurable
      (κ k) (hκstop k)
  have hEvent : MeasurableSet[𝓕.rightCont 0]
      (A ∩ {η : Ω | κ k η ≠ 0}) := hA.inter hPositive
  have hEventMeas : MeasurableSet
      (A ∩ {η : Ω | κ k η ≠ 0}) :=
    (𝓕.rightCont.le 0) _ hEvent
  have hGridZero (m : ℕ) :
      (∫ ω in A ∩ {η : Ω | κ k η ≠ 0},
        G m ω + J m ω ∂P) = 0 := by
    obtain ⟨S, a, b, WG, WJ, LG, LJ, hab, hWG, hWJ,
      hLG, hLJ, hWGbound, hWJbound, hGdef, hJdef⟩ := hStructures m
    obtain ⟨hMInt, hMG0, hJInt, hMJ0, hGridEvent⟩ :=
      hGrids S a b WG WJ hab hWG hWJ (κ k) (hκstop k)
        LG LJ hLG hLJ hWGbound hWJbound
    have hGeq : G m = (fun ω =>
        ∑ i ∈ S, (if κ k ω ≤ a i then 0 else WG i ω) *
          (R (b i) ω - R (a i) ω)) := funext hGdef
    have hJeq : J m = (fun ω =>
        ∑ i ∈ S, (if κ k ω ≤ a i then 0 else WJ i ω) *
          (Jsmall (b i) ω - Jsmall (a i) ω)) := funext hJdef
    simpa only [hGeq, hJeq] using hGridEvent A hA
  apply avram_b22_initial_event_finite_mesh_vanishing_error_budget
    (A ∩ {η : Ω | κ k η ≠ 0}) hEvent (w x) (H k)
    hHI.integrableOn (fun m ω => G m ω + J m ω) Err
  · intro m
    exact (hGI m |>.add (hJI m)).integrableOn
  · intro m
    exact (hEI m).integrableOn
  · exact hGridZero
  · intro m
    have hBound := hUpper m
    filter_upwards [ae_restrict_of_ae hBound,
      ae_restrict_mem hEventMeas] with ω hω hMem
    have hpos : 0 < κ k ω := pos_iff_ne_zero.mpr hMem.2
    convert hω hpos using 1 <;> ring
  · exact
      avram_jump6_A_integrable_error_global_L1_controls_initial_event_signed_integral
        (A ∩ {η : Ω | κ k η ≠ 0}) hEventMeas Err hEI hESmall
