-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja20261118_original_finite_mixed_physical_mesh_L1_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T13:35:47.699827+00:00
-- url     : https://prove2.me/submissions/596a4e4f-d989-4b5c-ac8e-f0a6b4fc19bf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ja20261118_positive_clock_finite_mixed_mesh_L1_budget
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_clock_term_cash_pathwise_le
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_ruinclipped_predictable_two_noise_mesh_gains_zero_at_zero_stop
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

/-- Glue exact zero-time discounted right dividend cash to the positive-clock Ito mesh source. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (σ : Ω → ℝ≥0) (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0))) (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0)) (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω = Real.exp (-(q * (σ ω : ℝ))) * w (if σ ω = 0 ∨
              (σ ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (σ ω) ω - rightLimit D (σ ω) ω
          else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) (hFI : Integrable F P)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤) (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, Tendsto (fun k : ℕ =>
         avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω) atTop (𝓝 (R u ω)))
    (hJsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, Tendsto (fun k : ℕ =>
         avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω) atTop (𝓝 (Jsmall u ω))) :
    ∃ (G J E : ℕ → Ω → ℝ), (∀ k, Integrable (G k) P) ∧
      (∀ k, Integrable (J k) P) ∧ (∀ k, Integrable (E k) P) ∧ (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m l : ℕ,
        N ≤ m → N ≤ l → (∫ ω, ‖G m ω - G l ω‖ ∂P) ≤ ε) ∧ (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m l : ℕ,
        N ≤ m → N ≤ l → (∫ ω, ‖J m ω - J l ω‖ ∂P) ≤ ε) ∧ (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m : ℕ,
        N ≤ m → (∫ ω, ‖E m ω‖ ∂P) ≤ ε) ∧ (∀ k, ∃ (S : Finset ℕ) (a b : ℕ → ℝ≥0)
        (WG WJ : ℕ → Ω → ℝ) (LG LJ : ℝ), (∀ i ∈ S, a i ≤ b i) ∧
        (∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WG i)) ∧
        (∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WJ i)) ∧ 0 ≤ LG ∧ 0 ≤ LJ ∧
        (∀ i ∈ S, ∀ ω, ‖WG i ω‖ ≤ LG) ∧ (∀ i ∈ S, ∀ ω, ‖WJ i ω‖ ≤ LJ) ∧ (∀ ω, G k ω =
          ∑ i ∈ S, (if σ ω ≤ a i then 0 else WG i ω) * (R (b i) ω - R (a i) ω)) ∧ (∀ ω, J k ω =
          ∑ i ∈ S, (if σ ω ≤ a i then 0 else WJ i ω) * (Jsmall (b i) ω - Jsmall (a i) ω))) ∧
      (∀ k, ∀ᵐ ω ∂P,
        F ω ≤ w x + G k ω + J k ω + E k ω) := by
  classical
  obtain ⟨G,J,E,hGI,hJI,hEI,hGC,hJC,hEC,hMesh,hCashPos,hZeroE⟩ :=
    avram_ja20261118_positive_clock_finite_mixed_mesh_L1_budget
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn
      σ hσstop hσbound F hFsource hFI hFiniteActivity
      R Jsmall hRsource hJsource
  refine ⟨G,J,E,hGI,hJI,hEI,hGC,hJC,hEC,hMesh,?_⟩
  intro k
  filter_upwards [hCashPos k] with ω hPositive
  by_cases hz : σ ω = 0
  · obtain ⟨S,a,b,WG,WJ,LG,LJ,hOrd,hWG,hWJ,hLG,hLJ,hBoundG,hBoundJ,hG,hJ⟩ :=
      hMesh k
    have hPair :=
      avram_b24_original_ruinclipped_predictable_two_noise_mesh_gains_zero_at_zero_stop
        σ R Jsmall S a b WG WJ ω hz
    have hg : G k ω = 0 := (hG ω).trans hPair.1
    have hj : J k ω = 0 := (hJ ω).trans hPair.2
    have he : E k ω = 0 := hZeroE k ω hz
    let W : Ω → ℝ := fun η =>
      if σ η = 0 ∨ (σ η : ℝ≥0∞) < ruinTime X x D η
      then x + X.X (σ η) η - rightLimit D (σ η) η
      else riskProcess X x D (σ η) η
    let Cash : Ω → ℝ := fun η =>
      (∫⁻ s in paymentTimes (ruinTime X x D η) ∩ Iic (σ η : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D η)).toReal
    let Term : Ω → ℝ := fun η => Real.exp (-(q * (σ η : ℝ))) * w (W η)
    have hInitial : Term ω + Cash ω ≤ w x :=
      avram_ubv_hor3_original_zero_clock_term_cash_pathwise_le
        X x q w C D hD hjump σ W Cash Term
        (by intro η; rfl) (by intro η; rfl) (by intro η; rfl) ω hz
    have hF : F ω = Term ω + Cash ω := by
      simpa only [W, Cash, Term] using hFsource ω
    rw [hF, hg, hj, he]
    simpa using hInitial
  · have hp : 0 < σ ω := lt_of_le_of_ne (show 0 ≤ σ ω from zero_le) (Ne.symm hz)
    exact hPositive hp
