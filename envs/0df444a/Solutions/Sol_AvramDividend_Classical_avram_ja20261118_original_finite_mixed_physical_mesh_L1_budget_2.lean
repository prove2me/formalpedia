-- Prove2me | solution 2 for AvramDividend.Classical.avram_ja20261118_original_finite_mixed_physical_mesh_L1_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T17:29:17.542877+00:00
-- url     : https://prove2.me/submissions/36db0eb1-64ff-4638-8094-2d53f4333975
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_positive_stop_ruinclipped_predictable_mesh_signed_cash_source
import Theorems.Thm_AvramDividend_Classical_avram_b24_arbitrary_original_intrinsic_two_noise_stopped_finite_grid_integrable
import Theorems.Thm_AvramDividend_Classical_avram_b24_ae_convergent_integrably_dominated_original_gains_are_L1_cauchy
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_dominated_ae_two_noise_cash_excess_L1
import Theorems.Thm_AvramDividend_Classical_avram_p4_f8_original_exact_clock_zero_reward_le_initial
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0
  mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (hν :
  X.ν ≠ 0) (hσ : X.σ ≠ 0) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw0 : 0
  ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth :
  ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y →
  ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
  (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 < x)
  (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg :
  ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω))
  (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t
  ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
  (n : ℕ) (hn : 0 < n) (σ : Ω → ℝ≥0) (hσstop : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω :
  WithTop ℝ≥0))) (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0)) (F : Ω → ℝ) (hFsource : ∀ ω, F ω =
  Real.exp (-(q * (σ ω : ℝ))) * w (if σ ω = 0 ∨ (σ ω : ℝ≥0∞) < ruinTime X x D ω then x +
  X.X (σ ω) ω - rightLimit D (σ ω) ω else riskProcess X x D (σ ω) ω) + (∫⁻ s in
  paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s)))
  ∂(dividendMeasure D ω)).toReal) (hFI : Integrable F P) (hFiniteActivity : X.ν (Iio (0 :
  ℝ)) ≠ ⊤) (R Jsmall : ℝ≥0 → Ω → ℝ) (hRsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, Tendsto (fun k : ℕ =>
  avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω) atTop (𝓝 (R u ω))) (hJsource :
  ∀ᵐ ω ∂P, ∀ u : ℝ≥0, Tendsto (fun k : ℕ =>
  avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω) atTop (𝓝 (Jsmall u ω))) : ∃
  (G J E : ℕ → Ω → ℝ), (∀ k, Integrable (G k) P) ∧ (∀ k, Integrable (J k) P) ∧ (∀ k,
  Integrable (E k) P) ∧ (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m l : ℕ, N ≤ m → N ≤ l → (∫ ω, ‖G m ω
  - G l ω‖ ∂P) ≤ ε) ∧ (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m l : ℕ, N ≤ m → N ≤ l → (∫ ω, ‖J m ω -
  J l ω‖ ∂P) ≤ ε) ∧ (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m : ℕ, N ≤ m → (∫ ω, ‖E m ω‖ ∂P) ≤ ε) ∧ (∀
  k, ∃ (S : Finset ℕ) (a b : ℕ → ℝ≥0) (WG WJ : ℕ → Ω → ℝ) (LG LJ : ℝ), (∀ i ∈ S, a i ≤ b i)
  ∧ (∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WG i)) ∧ (∀ i ∈ S, Measurable[𝓕.rightCont (a
  i)] (WJ i)) ∧ 0 ≤ LG ∧ 0 ≤ LJ ∧ (∀ i ∈ S, ∀ ω, ‖WG i ω‖ ≤ LG) ∧ (∀ i ∈ S, ∀ ω, ‖WJ i ω‖ ≤
  LJ) ∧ (∀ ω, G k ω = ∑ i ∈ S, (if σ ω ≤ a i then 0 else WG i ω) * (R (b i) ω - R (a i) ω))
  ∧ (∀ ω, J k ω = ∑ i ∈ S, (if σ ω ≤ a i then 0 else WJ i ω) * (Jsmall (b i) ω - Jsmall (a
  i) ω))) ∧ (∀ k, ∀ᵐ ω ∂P, F ω ≤ w x + G k ω + J k ω + E k ω) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨MG, MJ, BG, BJ, G, J, E, hGlim, hJlim, hElim,
    hBGI, hBJI, hGdom, hJdom, hMesh, hZero, hPositive⟩ :=
    avram_b24_original_positive_stop_ruinclipped_predictable_mesh_signed_cash_source
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg
      hjump n hn σ hσstop hσbound F hFsource hFI
      hFiniteActivity R Jsmall hRsource hJsource
  have hGJI : ∀ k, Integrable (G k) P ∧ Integrable (J k) P := by
    intro k
    obtain ⟨S, a, b, WG, WJ, LG, LJ, hab, hwg, hwj,
      hlg, hlj, hwgb, hwjb, hg, hj⟩ := hMesh k
    have hBoth :=
      avram_b24_arbitrary_original_intrinsic_two_noise_stopped_finite_grid_integrable
        X hX hFiniteActivity R Jsmall hRsource hJsource
        S a b WG WJ hab hwg hwj σ hσstop LG LJ hlg hlj hwgb hwjb
    have hGeq : G k = (fun ω => ∑ i ∈ S,
        (if σ ω ≤ a i then 0 else WG i ω) *
          (R (b i) ω - R (a i) ω)) := funext hg
    have hJeq : J k = (fun ω => ∑ i ∈ S,
        (if σ ω ≤ a i then 0 else WJ i ω) *
          (Jsmall (b i) ω - Jsmall (a i) ω)) := funext hj
    constructor
    · rw [hGeq]
      exact hBoth.1
    · rw [hJeq]
      exact hBoth.2
  have hGI : ∀ k, Integrable (G k) P := fun k => (hGJI k).1
  have hJI : ∀ k, Integrable (J k) P := fun k => (hGJI k).2
  have hGC :=
    (avram_b24_ae_convergent_integrably_dominated_original_gains_are_L1_cauchy
      P G MG BG hGI hBGI hGdom hGlim).2
  have hJC :=
    (avram_b24_ae_convergent_integrably_dominated_original_gains_are_L1_cauchy
      P J MJ BJ hJI hBJI hJdom hJlim).2
  have hFzero : ∀ ω, σ ω = 0 → F ω ≤ w x := by
    intro ω hσzero
    exact (avram_p4_f8_original_exact_clock_zero_reward_le_initial
      X x q w C D hD hjump (fun _ => σ) (fun _ => F)
      (fun _ ω => hFsource ω)) 0 ω hσzero
  have hFull : ∀ k, ∀ᵐ ω ∂P,
      F ω ≤ w x + G k ω + J k ω + E k ω := by
    intro k
    filter_upwards [hZero k, hPositive k] with ω hz hp
    by_cases hσzero : σ ω = 0
    · obtain ⟨hg, hj, he⟩ := hz hσzero
      rw [hg, hj, he]
      simpa using hFzero ω hσzero
    · exact hp (lt_of_le_of_ne (show 0 ≤ σ ω from zero_le) (Ne.symm hσzero))
  let Epos : ℕ → Ω → ℝ :=
    fun k ω => max (F ω - w x - G k ω - J k ω) 0
  obtain ⟨hEI, hCash, hEtendsto⟩ :=
    avram_b24_original_dominated_ae_two_noise_cash_excess_L1
      P F (w x) G J E MG MJ BG BJ
      hFI hGI hJI hBGI hBJI hGdom hJdom
      hGlim hJlim hElim hFull
  have hEsmall : ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
        (∫ ω, ‖Epos m ω‖ ∂P) ≤ ε := by
    intro ε hε
    have hEvent : ∀ᶠ m in atTop,
        (∫ ω, ‖Epos m ω‖ ∂P) < ε :=
      hEtendsto.eventually (Iio_mem_nhds hε)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hEvent
    exact ⟨N, fun m hm => le_of_lt (hN m hm)⟩
  exact ⟨G, J, Epos, hGI, hJI, hEI,
    hGC, hJC, hEsmall, hMesh, hCash⟩
