-- Prove2me | solution 2 for AvramDividend.Classical.avram_jb19_original_spatial_two_noise_ledger
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T13:23:08.501795+00:00
-- url     : https://prove2.me/submissions/fd19002f-85f1-4587-bc80-0e63724d3bb6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b236_original_ruinclipped_bounded_predictable_mesh_ito_cash_domination_source
import Theorems.Thm_AvramDividend_Classical_avram_b218_original_bounded_weight_intrinsic_two_noise_stopped_grid_centering
import Theorems.Thm_AvramDividend_Classical_avram_b69_original_true_spatial_clock_ruin_clipped
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin36_original_finitecap_any_stopped_full_reward_L1
import Theorems.Thm_AvramDividend_Classical_avram_jb23_dominated_two_channel_initial_centering_L1
import Theorems.Thm_AvramDividend_Classical_avram_jb24_stopped_cash_limit_upper_from_two_noises
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Root-linked finite mixed original ruin-clipped stopped two-noise ledger. -/
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
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) :
    ∀ (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A → ∀ k, Integrable (H k) P ∧ ∃ MG MJ B : Ω → ℝ,
          Integrable MG P ∧ Integrable MJ P ∧ P[MG | 𝓕.rightCont 0] =ᵐ[P] 0 ∧
          P[MJ | 𝓕.rightCont 0] =ᵐ[P] 0 ∧ (∀ᵐ ω ∂(P.restrict (A ∩ {η : Ω | κ k η ≠ 0})), B ω ≤ 0) ∧
          (∀ᵐ ω ∂(P.restrict (A ∩ {η : Ω | κ k η ≠ 0})), H k ω ≤ w x + MG ω + MJ ω + B ω) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨R, Jsmall, hRsource, hJsource, hCenter⟩ :=
    avram_b218_original_bounded_weight_intrinsic_two_noise_stopped_grid_centering
      X hX hFiniteActivity
  intro A hA k
  have hClip := avram_b69_original_true_spatial_clock_ruin_clipped X x D n ρ hρclip κ hκexact
  have hκbound : ∀ ω, κ k ω ≤ (n : ℝ≥0) := by
    intro ω
    exact (hClip k ω).1.trans (hρbound ω)
  have hκclip : ∀ ω, κ k ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal := by
    intro ω
    exact (hClip k ω).1.trans (hρclip ω)
  have hHI : Integrable (H k) P :=
    avram_mix_fin36_original_finitecap_any_stopped_full_reward_L1
      X x q (le_of_lt hq) w hw_cont hw_neg
      C hCfinite hxc D hD n (κ k) (hκstop k)
      hκbound (H k) (hHsource k)
  obtain ⟨MG,MJ,BG,BJ,G,J,E,hGA,hJA,hEA,hBG,hBJ,hGD,hJD,hMesh,hCash⟩ :=
    avram_b236_original_ruinclipped_bounded_predictable_mesh_ito_cash_domination_source
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn
      (κ k) (hκstop k) hκbound hκclip
      (H k) (hHsource k) hHI hFiniteActivity
      R Jsmall hRsource hJsource
  have hGains (j : ℕ) :
      Integrable (G j) P ∧
      P[G j | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)) ∧
      Integrable (J j) P ∧
      P[J j | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)) := by
    obtain ⟨S,a,b,WG,WJ,LG,LJ,hab,hWG,hWJ,hLG,hLJ,hGB,hJB,hGs,hJs⟩ := hMesh j
    have h := hCenter S a b WG WJ hab hWG hWJ
      (κ k) (hκstop k) LG LJ hLG hLJ hGB hJB
    simpa only [← hGs, ← hJs] using h
  obtain ⟨hMGI,hMG0,hMJI,hMJ0⟩ :=
    avram_jb23_dominated_two_channel_initial_centering_L1
      G J MG MJ BG BJ
      (fun j => (hGains j).1)
      (fun j => (hGains j).2.2.1)
      hGA hJA hBG hBJ hGD hJD
      (fun j => (hGains j).2.1)
      (fun j => (hGains j).2.2.2)
  have hUpper : ∀ᵐ ω ∂P, H k ω ≤ w x + MG ω + MJ ω :=
    avram_jb24_stopped_cash_limit_upper_from_two_noises
      (w x) (H k) MG MJ G J E hGA hJA hEA hCash
  refine ⟨hHI,MG,MJ,(fun _ => 0),hMGI,hMJI,hMG0,hMJ0,?_,?_⟩
  · filter_upwards [] with ω
    exact le_refl 0
  · filter_upwards [ae_restrict_of_ae hUpper] with ω h
    simpa only [add_zero] using h
