-- Prove2me | solution 5 for AvramDividend.Classical.avram_gfinite61_original_fixed_band_cash_with_explicit_occupation_cost
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T10:06:24.397794+00:00
-- url     : https://prove2.me/submissions/e631848e-21d1-4586-b94d-4245d8723cd2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gb20_original_finitecap_postpaid_grid_L1_limit
import Theorems.Thm_AvramDividend_Classical_avram_lsc_public_original_charged_source_L1
import Theorems.Thm_AvramDividend_Classical_avram_gbB54w_original_finitecap_discounted_cash_corner_strip_integrable
import Theorems.Thm_AvramDividend_Classical_avram_lsc_abstract_integrable_charged_mesh_L1_budget
import Theorems.Thm_AvramDividend_Classical_avram_gb26_original_finitecap_strip_event_integrable
import Theorems.Thm_AvramDividend_Classical_avram_gfinite42_original_compact_diagonal_gaussian_grid_centered
import Theorems.Thm_AvramDividend_Classical_avram_gfinite45_original_cash_residual_integrable
import Theorems.Thm_AvramDividend_Classical_avram_gbB37_original_finitecap_interior_clip_gap_nonnegative
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq
: 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧
ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x
: ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump
: ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 < n) (τ : Ω →
ℝ≥0) (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (hτmeas : Measurable (fun ω => (τ ω : ℝ))) (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (σ : ℕ → Ω → ℝ≥0)
(hσstop : ∀ k, IsStoppingTime 𝓕.rightCont (fun ω => (σ k ω : WithTop ℝ≥0))) (hσle : ∀ k ω, σ k ω ≤ τ ω) : ∀ k (ρ : Ω → ℝ≥0) (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) (hρle :
∀ ω, ρ ω ≤ σ k ω) (δ : ℝ) (hδ : 0 < δ) (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω → δ ≤ riskProcess X x D t ω) (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A → ∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ (K : ℕ), ∃ (m :
ℕ), K < m ∧
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
        let a : ℝ := δ / 2
        let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        let Y : ℕ → Ω → ℝ := fun i ω => x + X.X (s i) ω - rightLimit D (s i) ω
        let Z : ℕ → Ω → ℝ := fun i ω => X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c
        let G : ℕ → Ω → ℝ := fun i ω => if s i < ρ ω then Real.exp (-(q * (s i : ℝ))) * (if Y i ω ∈ Icc a b then deriv w (Y i ω) else 1) else 0
        let H : ℕ → Ω → ℝ := fun i ω => if s i < ρ ω then (1 / 2 : ℝ) * Real.exp (-(q * (s i : ℝ))) * (if Y i ω ∈ Icc a b then iteratedDeriv 2 w (Y i ω) else 0) else 0
        let M : Ω → ℝ := fun ω =>
          (Finset.range (m + 1)).sum (fun i => G i ω * Z i ω + H i ω * (Z i ω ^ 2 - (Δ : ℝ) * X.σ ^ 2))
        let F : Ω → ℝ := fun ω => if ρ ω = 0 then w x else Real.exp (-(q * (ρ ω : ℝ))) * w (riskProcess X x D (ρ ω) ω) + (∫⁻ z in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * z))) ∂(dividendMeasure D ω)).toReal
        let Occ : Ω → ℝ := fun ω => ∫ t in Ioo (0 : ℝ) (n : ℝ), if t < (ρ ω : ℝ) ∧ b < riskProcess X x D (Real.toNNReal t) ω then (1 : ℝ) else 0 ∂volume
        (∫ ω in A, max (F ω - w x - M ω) 0 ∂P) ≤ (w C.toReal - w b) - (C.toReal - b) + max X.c 0 * (∫ ω in A, Occ ω ∂P) + ε := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro k ρ hρstop hρle δ hδ hFloor A hA j ε hε K
  let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  let M : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let a : ℝ := δ / 2
    let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    let Y : ℕ → Ω → ℝ := fun i η => x + X.X (s i) η - rightLimit D (s i) η
    let Z : ℕ → Ω → ℝ := fun i η => X.X (s i + Δ) η - X.X (s i) η - (Δ : ℝ) * X.c
    let G : ℕ → Ω → ℝ := fun i η =>
      if s i < ρ η then Real.exp (-(q * (s i : ℝ))) *
        (if Y i η ∈ Icc a b then deriv w (Y i η) else 1) else 0
    let H : ℕ → Ω → ℝ := fun i η =>
      if s i < ρ η then (1 / 2 : ℝ) * Real.exp (-(q * (s i : ℝ))) *
        (if Y i η ∈ Icc a b then iteratedDeriv 2 w (Y i η) else 0) else 0
    (Finset.range (m + 1)).sum (fun i =>
      G i ω * Z i ω + H i ω * (Z i ω ^ 2 - (Δ : ℝ) * X.σ ^ 2))
  let F : Ω → ℝ := fun ω =>
    if ρ ω = 0 then w x else Real.exp (-(q * (ρ ω : ℝ))) * w (riskProcess X x D (ρ ω) ω) +
      (∫⁻ z in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * z))) ∂(dividendMeasure D ω)).toReal
  let Occ : Ω → ℝ := fun ω =>
    ∫ t in Ioo (0 : ℝ) (n : ℝ),
      if t < (ρ ω : ℝ) ∧ b < riskProcess X x D (Real.toNNReal t) ω
      then (1 : ℝ) else 0 ∂volume
  obtain ⟨N, hNI, _, hConverge⟩ := avram_gb20_original_finitecap_postpaid_grid_L1_limit
      X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg hw_smooth hw_gen
      hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas hτstop σ hσstop
      hσle k ρ hρstop hρle δ hδ hFloor A hA j
  have hL1 := hConverge
  let B : Ω → ℝ := fun ω => ((w C.toReal - w b) - (C.toReal - b)) + max X.c 0 * Occ ω
  have hMInt (m : ℕ) : IntegrableOn (M m) A P := by
    obtain ⟨hGridInt, _⟩ := avram_gfinite42_original_compact_diagonal_gaussian_grid_centered
        X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn
      τ hτeq hτmeas hτstop σ hσstop hσle
      k ρ hρstop hρle δ hδ hFloor A hA (fun _ => m)
    simpa [M] using hGridInt j
  have hFBI :=
    avram_gbB54w_original_finitecap_discounted_cash_corner_strip_integrable
      X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas
      hτstop σ hσstop hσle k ρ hρstop hρle δ hδ hFloor A hA j
  have hR :=
    avram_lsc_public_original_charged_source_L1
      X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas
      hτstop σ hσstop hσle k ρ hρstop hρle δ hδ hFloor A hA j
  have hFI (m : ℕ) : IntegrableOn (fun ω => max ((F ω - w x) - M m ω) 0) A P := by
    have hGridInt :=
      avram_gfinite45_original_cash_residual_integrable
        X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn
      τ hτeq hτmeas hτstop σ hσstop hσle
      k ρ hρstop hρle δ hδ hFloor A hA (fun _ => m)
    simpa [M, F, sub_sub] using hGridInt j
  obtain ⟨hOccI, hOccBound⟩ :=
    avram_gb26_original_finitecap_strip_event_integrable
      X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn
      τ hτeq hτmeas hτstop σ hσstop hσle
      k ρ hρstop hρle δ hδ hFloor A hA j
  have hOccNonneg : ∀ᵐ ω ∂(P.restrict A), 0 ≤ Occ ω := Filter.Eventually.of_forall (fun ω => (hOccBound ω).1)
  obtain ⟨m, hm, hEstimate⟩ :=
    avram_lsc_abstract_integrable_charged_mesh_L1_budget
      P A (fun ω => F ω - w x) N Occ M
      ((w C.toReal - w b) - (C.toReal - b)) (max X.c 0)
      (by simpa [b] using
        (avram_gbB37_original_finitecap_interior_clip_gap_nonnegative
          C hC hFiniteCap w hw_cont hw_smooth hw_grad j).2.2)
      (le_max_right _ _)
      (by
        change Integrable (fun ω => (F ω - w x) - B ω) (P.restrict A)
        simpa [F, B, Occ, b] using hFBI) hNI.integrableOn hMInt hL1
      (by simpa [M, F, B, Occ, b, sub_sub] using hR) hFI (by simpa [Occ, b] using hOccI) hOccNonneg ε hε K
  exact ⟨m, hm, by simpa [M, F, Occ, b, sub_sub] using hEstimate⟩
