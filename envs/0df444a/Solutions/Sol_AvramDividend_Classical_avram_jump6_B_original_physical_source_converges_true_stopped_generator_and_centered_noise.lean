-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_physical_source_converges_true_stopped_generator_and_centered_noise
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T19:04:10.586565+00:00
-- url     : https://prove2.me/submissions/f51df265-9da4-4bf8-a9f3-33931af92725
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_finite_physical_source_L1_compensator_and_drift_diagonal
import Theorems.Thm_AvramDividend_Classical_avram_gaussian12_restricted_L1_limit_preserves_zero_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0)
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
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P)
    (hInfiniteActivity : X.ν (Iio (0 : ℝ)) = ⊤) : ∀ k : ℕ,
      let Cash : Ω → ℝ := fun ω : Ω =>
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
      let u : ℕ → ℕ → ℝ≥0 := fun j i =>
        (i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)
      let m : ℕ → ℕ := fun j => (n + 1) * (j + 1)
      let Source : ℕ → Ω → ℝ := fun n ω =>
      let v : ℕ → ℝ≥0 := fun i => min (u n i) (σ k ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      ∑ i ∈ Finset.range (m n),
        ((E (v (i + 1)) - E (v i)) * w (Y (v i)) +
          E (v (i + 1)) * (w (Z i) - w (Y (v i))))
      ∃ μ : Measure ℝ≥0,
        μ {(0 : ℝ≥0)} = 0 ∧
        let Y : ℝ≥0 → Ω → ℝ := fun t ω =>
          Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s ω - rightLimit D s ω) t
        let G : Ω → ℝ := fun ω => ∫ t : ℝ≥0,
          if 0 < Y t ω ∧ ENNReal.ofReal (Y t ω) < C ∧ t ≤ σ k ω then
            Real.exp (-(q * (t : ℝ))) *
              (X.generator w (Y t ω) - q * w (Y t ω))
          else 0 ∂μ
        ∃ Mc : Ω → ℝ,
          Integrable Mc P ∧ Integrable G P ∧
          (∫ ω, Mc ω ∂P) = 0 ∧
          (∀ᵐ ω ∂P, Tendsto (fun j => Source j ω) atTop (𝓝 (Mc ω + G ω))) := by
  intro k; dsimp only
  let Cash : Ω → ℝ := fun ω =>
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
  let u : ℕ → ℕ → ℝ≥0 := fun j i => (i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)
  let m : ℕ → ℕ := fun j => (n + 1) * (j + 1)
  let Source : ℕ → Ω → ℝ := fun n ω =>
    let v : ℕ → ℝ≥0 := fun i => min (u n i) (σ k ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    ∑ i ∈ Finset.range (m n),
      ((E (v (i + 1)) - E (v i)) * w (Y (v i)) +
        E (v (i + 1)) * (w (Z i) - w (Y (v i))))
  obtain ⟨μ, hμ0, M, Mc, hMInt, hMmean, hMcI, hGI, hL1,
    hMPoint, hResidual⟩ :=
    avram_jump6_B_original_finite_physical_source_L1_compensator_and_drift_diagonal
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτstop σ F hσstop hσle hFsource hFI
      hInfiniteActivity k
  have hMcMean : (∫ ω, Mc ω ∂P) = 0 := by
    have h :=
      avram_gaussian12_restricted_L1_limit_preserves_zero_mean
        Set.univ MeasurableSet.univ M hMInt Mc hMcI
        (by intro j; simpa using hMmean j)
        (by simpa using hL1)
    simpa using h
  refine ⟨μ, hμ0, Mc, hMcI, hGI, hMcMean, ?_⟩
  filter_upwards [hMPoint, hResidual] with ω hMω hRω
  have hSum := hMω.add hRω
  convert hSum using 1
  funext j; ring
