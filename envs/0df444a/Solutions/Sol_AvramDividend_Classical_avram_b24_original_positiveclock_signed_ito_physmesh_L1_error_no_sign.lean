-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_positiveclock_signed_ito_physmesh_L1_error_no_sign
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:19:49.652019+00:00
-- url     : https://prove2.me/submissions/80d78b88-0afe-4fd8-be5d-8caa245daa9a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b219_original_bounded_predictable_mesh_ito_cash_domination_source
import Theorems.Thm_AvramDividend_Classical_avram_b24_arbitrary_original_intrinsic_two_noise_stopped_finite_grid_integrable
import Theorems.Thm_AvramDividend_Classical_avram_b24_ae_convergent_integrably_dominated_original_gains_are_L1_cauchy
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_dominated_ae_two_noise_cash_excess_L1
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X :
    SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ :
    X.σ ≠ 0) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw0 : 0 ≤ w 0) (hw_cont :
    ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 <
    y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
    X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y →
    ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D :
    ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) <
    ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) <
    ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D
    t ω - (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 < n) (σ : Ω → ℝ≥0) (hσstop : IsStoppingTime
    𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0))) (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0)) (hσclip : ∀ ω, σ ω
    ≤ (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (F : Ω → ℝ) (hFsource : ∀ ω, F ω = Real.exp
    (-(q * (σ ω : ℝ))) * w (if σ ω = 0 ∨ (σ ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (σ ω) ω -
    rightLimit D (σ ω) ω else riskProcess X x D (σ ω) ω) + (∫⁻ s in paymentTimes (ruinTime X x D ω)
    ∩ Iic (σ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) (hFI :
    Integrable F P) (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤) (R Jsmall : ℝ≥0 → Ω → ℝ) (hRsource :
    ∀ᵐ ω ∂P, ∀ u : ℝ≥0, Tendsto (fun k : ℕ => avram_p4_h_gaussian_intrinsic_truncated_residual X k
    u ω) atTop (𝓝 (R u ω))) (hJsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, Tendsto (fun k : ℕ =>
    avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω) atTop (𝓝 (Jsmall u ω))) : ∃ (G J
    E : ℕ → Ω → ℝ), (∀ m, Integrable (E m) P) ∧ (∀ m, ∃ (S : Finset ℕ) (a b : ℕ → ℝ≥0) (WG WJ : ℕ →
    Ω → ℝ) (LG LJ : ℝ), (∀ i ∈ S, a i ≤ b i) ∧ (∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WG i)) ∧ (∀
    i ∈ S, Measurable[𝓕.rightCont (a i)] (WJ i)) ∧ 0 ≤ LG ∧ 0 ≤ LJ ∧ (∀ i ∈ S, ∀ ω, ‖WG i ω‖ ≤ LG)
    ∧ (∀ i ∈ S, ∀ ω, ‖WJ i ω‖ ≤ LJ) ∧ (∀ ω, G m ω = ∑ i ∈ S, (if σ ω ≤ a i then 0 else WG i ω) * (R
    (b i) ω - R (a i) ω)) ∧ (∀ ω, J m ω = ∑ i ∈ S, (if σ ω ≤ a i then 0 else WJ i ω) * (Jsmall (b
    i) ω - Jsmall (a i) ω))) ∧ (∀ m, ∀ᵐ ω ∂P, 0 < σ ω → F ω ≤ w x + G m ω + J m ω + E m ω) ∧ (∀ ε :
    ℝ, 0 < ε → ∃ N : ℕ, ∀ m l : ℕ, N ≤ m → N ≤ l → (∫ ω, ‖G m ω - G l ω‖ ∂P) ≤ ε) ∧ (∀ ε : ℝ, 0 < ε
    → ∃ N : ℕ, ∀ m l : ℕ, N ≤ m → N ≤ l → (∫ ω, ‖J m ω - J l ω‖ ∂P) ≤ ε) ∧ (∀ ε : ℝ, 0 < ε → ∃ N :
    ℕ, ∀ m : ℕ, N ≤ m → (∫ ω, ‖E m ω‖ ∂P) ≤ ε) := by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨MG, MJ, BG, BJ, G, J, Err, hGa, hJa, hEa,
      hBGI, hBJI, hGB, hJB, hGrid, hCash⟩ :=
    AvramDividend.Classical.avram_b219_original_bounded_predictable_mesh_ito_cash_domination_source
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn σ hσstop hσbound F hFsource hFI hFiniteActivity
      R Jsmall hRsource hJsource
  have hGainI (m : ℕ) :
      Integrable (G m) P ∧ Integrable (J m) P := by
    obtain ⟨S, a, b, WG, WJ, LG, LJ, hab, hWG, hWJ,
        hLG, hLJ, hWGbound, hWJbound, hGform, hJform⟩ := hGrid m
    obtain ⟨hGI, hJI⟩ :=
      AvramDividend.Classical.avram_b24_arbitrary_original_intrinsic_two_noise_stopped_finite_grid_integrable
        X hX hFiniteActivity R Jsmall hRsource hJsource
        S a b WG WJ hab hWG hWJ σ hσstop LG LJ
        hLG hLJ hWGbound hWJbound
    refine ⟨hGI.congr ?_, hJI.congr ?_⟩
    · filter_upwards [] with ω
      exact (hGform ω).symm
    · filter_upwards [] with ω
      exact (hJform ω).symm
  have hCauchyG :=
    AvramDividend.Classical.avram_b24_ae_convergent_integrably_dominated_original_gains_are_L1_cauchy
      P G MG BG (fun m => (hGainI m).1) hBGI hGB hGa
  have hCauchyJ :=
    AvramDividend.Classical.avram_b24_ae_convergent_integrably_dominated_original_gains_are_L1_cauchy
      P J MJ BJ (fun m => (hGainI m).2) hBJI hJB hJa
  have hError :=
    AvramDividend.Classical.avram_b24_original_dominated_ae_two_noise_cash_excess_L1
      P F (w x) G J Err MG MJ BG BJ hFI
      (fun m => (hGainI m).1) (fun m => (hGainI m).2)
      hBGI hBJI hGB hJB hGa hJa hEa hCash
  let Epos : ℕ → Ω → ℝ := fun m ω =>
    max (F ω - w x - G m ω - J m ω) 0
  change (∀ m, Integrable (Epos m) P) ∧
    (∀ m, ∀ᵐ ω ∂P, F ω ≤ w x + G m ω + J m ω + Epos m ω) ∧
    Tendsto (fun m => ∫ ω, ‖Epos m ω‖ ∂P) atTop (𝓝 0)
    at hError
  refine ⟨G, J, Epos, hError.1, hGrid, ?_,
    hCauchyG.2, hCauchyJ.2, ?_⟩
  · intro m
    filter_upwards [hError.2.1 m] with ω hw
    exact fun _ => hw
  · intro ε hε
    obtain ⟨N, hN⟩ :=
      Filter.eventually_atTop.mp
        (hError.2.2.eventually (Iio_mem_nhds hε))
    exact ⟨N, fun m hm => le_of_lt (hN m hm)⟩
