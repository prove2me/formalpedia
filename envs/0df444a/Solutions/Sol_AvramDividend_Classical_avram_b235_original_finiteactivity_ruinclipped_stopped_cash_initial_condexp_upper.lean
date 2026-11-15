-- Prove2me | solution 1 for AvramDividend.Classical.avram_b235_original_finiteactivity_ruinclipped_stopped_cash_initial_condexp_upper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:39:08.686128+00:00
-- url     : https://prove2.me/submissions/09eac37a-0d21-41f8-851e-650735235f27
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_avram_b218_original_bounded_weight_intrinsic_two_noise_stopped_grid_centering
import Theorems.Thm_AvramDividend_Classical_avram_b236_original_ruinclipped_bounded_predictable_mesh_ito_cash_domination_source
import Theorems.Thm_AvramDividend_Classical_avram_jb24_finite_mesh_stopped_cash_condexp_upper
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n)
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0))
    (hσclip : ∀ ω, σ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨
              (σ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ ω) ω - rightLimit D (σ ω) ω
          else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : Integrable F P)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P F ω ≤ w x := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨R, Jsmall, hRlim, hJlim, hCentered⟩ :=
    avram_b218_original_bounded_weight_intrinsic_two_noise_stopped_grid_centering
      X hX hFiniteActivity
  obtain ⟨MG, MJ, BG, BJ, G, J, E, hGconv, hJconv, hEconv,
      hBG, hBJ, hGdom, hJdom, hRep, hUpper⟩ :=
    avram_b236_original_ruinclipped_bounded_predictable_mesh_ito_cash_domination_source
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn σ hσstop hσbound hσclip F hFsource hFI hFiniteActivity
      R Jsmall hRlim hJlim
  have hPair (k : ℕ) :
      Integrable (G k) P ∧
      P[G k | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)) ∧
      Integrable (J k) P ∧
      P[J k | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)) := by
    obtain ⟨S, a, b, WG, WJ, LG, LJ, hab, hWG, hWJ,
      hLG, hLJ, hWGbound, hWJbound, hGeq, hJeq⟩ := hRep k
    have hGfun : G k = (fun ω =>
        ∑ i ∈ S, (if σ ω ≤ a i then 0 else WG i ω) *
          (R (b i) ω - R (a i) ω)) := funext hGeq
    have hJfun : J k = (fun ω =>
        ∑ i ∈ S, (if σ ω ≤ a i then 0 else WJ i ω) *
          (Jsmall (b i) ω - Jsmall (a i) ω)) := funext hJeq
    simpa only [hGfun, hJfun] using
      (hCentered S a b WG WJ hab hWG hWJ
        σ hσstop LG LJ hLG hLJ hWGbound hWJbound)
  obtain ⟨_, _, _, _, hBound⟩ :=
    avram_jb24_finite_mesh_stopped_cash_condexp_upper
      (𝓕 := 𝓕) (w x) F MG MJ BG BJ G J E hFI
      (fun k => (hPair k).1) (fun k => (hPair k).2.2.1)
      hGconv hJconv hEconv hBG hBJ hGdom hJdom
      (fun k => (hPair k).2.1) (fun k => (hPair k).2.2.2)
      hUpper
  exact hBound
