-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_original_zerojump_finitecap_signed_physical_ito_mesh_expected_source
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:57:05.699187+00:00
-- url     : https://prove2.me/submissions/95ca9f81-b450-4c92-8986-0d1a864692fc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_stop_original_cells_F0_centred
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_zerojump_signed_stopped_physical_mesh_error_source
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq :
  0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
  (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y <
  C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator
  w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ)
  (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
  (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t
  ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω
  ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (n : ℕ)
  (hn : 0 < n) (τ : Ω → ℝ≥0) (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
  (hτmeas : Measurable (fun ω => (τ ω : ℝ))) (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω
  : WithTop ℝ≥0))) (W Cash Term : Ω → ℝ) (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X
  x D ω then x + X.X (τ ω) ω - rightLimit D (τ ω) ω else riskProcess X x D (τ ω) ω) (hCash : ∀
  ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ), ENNReal.ofReal (Real.exp
  (-(q * s))) ∂(dividendMeasure D ω)).toReal) (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ)))
  * w (W ω)) (hTermMeas : AEStronglyMeasurable Term P) (hCashI : Integrable Cash P) (σ : ℕ → Ω →
  ℝ≥0) (F : ℕ → Ω → ℝ) (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont (fun ω => (σ k ω : WithTop
  ℝ≥0))) (hσle : ∀ k ω, σ k ω ≤ τ ω) (hFsource : ∀ k ω, F k ω = Real.exp (-(q * (σ k ω : ℝ))) *
  w (if σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (σ k ω) ω - rightLimit D (σ k
  ω) ω else riskProcess X x D (σ k ω) ω) + (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω
  : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) (hFI : ∀ k,
  Integrable (F k) P) (hν : X.ν = 0) (hFinite : C ≠ ⊤) : ∀ k, ∃ (S : ℕ → Finset ℕ) (τg : ℕ → ℕ →
  Ω → ℝ≥0) (h : ℕ → ℕ → ℝ≥0) (G H : ℕ → ℕ → Ω → ℝ) (Q E : ℕ → Ω → ℝ), (∀ j ω, Q j ω = ∑ i ∈ S j,
  (let Z : ℝ := (X.X (τg j i ω + h j i) ω - ((τg j i ω + h j i : ℝ≥0) : ℝ) * X.c) - (X.X (τg j i
  ω) ω - (τg j i ω : ℝ) * X.c); G j i ω * Z + H j i ω * (Z ^ 2 - ((h j i : ℝ) * X.σ ^ 2)))) ∧ (∀
  j, Integrable (Q j) P) ∧ (∀ j, (∫ ω, Q j ω ∂P) = 0) ∧ (∀ j, Integrable (E j) P) ∧ Tendsto (fun
  j => ∫ ω, E j ω ∂P) Filter.atTop (nhds (0 : ℝ)) ∧ (∀ j, ∀ᵐ ω ∂P, F k ω ≤ w x + Q j ω + E j ω) := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro k
  obtain ⟨S, τg, B, h, G, H, M, E, hτg, hBound, hG, hH,
    hM, hGI, hHI, hH2I, hEI, hElim, hLedger⟩ :=
    avram_a21_original_zerojump_signed_stopped_physical_mesh_error_source
      X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn
      τ hτeq hτmeas hτstop W Cash Term hW hCash hTerm
      hTermMeas hCashI σ F hσstop hσle hFsource hFI hν hFinite k
  let Q : ℕ → Ω → ℝ := fun j ω =>
    ∑ i ∈ S j, (G j i ω * M j i ω +
      (H j i ω * (M j i ω)^2 - ((h j i : ℝ) * X.σ^2) * H j i ω))
  have hQI (j : ℕ) : Integrable (Q j) P ∧
      condExp (𝓕.rightCont 0) P (Q j) =ᵐ[P]
        (fun _ => (0 : ℝ)) := by
    simpa only [Q] using
      (avram_ubv_gauss13_stop_original_cells_F0_centred
        X hν (S j) (τg j) (hτg j) (B j)
        (hBound j) (h j) (G j) (H j) (hG j) (hH j)
        (M j) (hM j) (hGI j) (hHI j) (hH2I j))
  have hMean (j : ℕ) : (∫ ω, Q j ω ∂P) = 0 := by
    have hF0 : 𝓕.rightCont 0 ≤ mΩ := 𝓕.rightCont.le 0
    calc
      _ = ∫ ω, condExp (𝓕.rightCont 0) P (Q j) ω ∂P :=
        (integral_condExp (μ := P) (f := Q j) hF0).symm
      _ = 0 := by
        rw [integral_congr_ae (hQI j).2]
        simp
  refine ⟨S, τg, h, G, H, Q, E, ?_,
    (fun j => (hQI j).1), hMean, hEI, hElim, ?_⟩
  · intro j ω
    dsimp [Q]
    apply Finset.sum_congr rfl
    intro i hi
    rw [congrFun (congrFun (hM j) i) ω]
    ring
  · intro j
    simpa only [Q] using hLedger j
