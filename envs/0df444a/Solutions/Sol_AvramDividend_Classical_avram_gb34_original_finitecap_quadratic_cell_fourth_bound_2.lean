-- Prove2me | solution 2 for AvramDividend.Classical.avram_gb34_original_finitecap_quadratic_cell_fourth_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T11:05:31.009285+00:00
-- url     : https://prove2.me/submissions/0dbc1ae6-3e0c-4b2b-83d5-d8413e40ac57

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gb40_original_bounded_hessian_stopped_weight
import Theorems.Thm_AvramDividend_Classical_avram_gb42_bounded_original_gaussian_quadratic_cell
import Theorems.Thm_AvramDividend_Classical_avram_gb43_finitecap_compact_interior_band
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_general_interval_fourth_moment_le_three_dt_sq
import Theorems.Thm_AvramDividend_Classical_avram_gauss_endpoint_sigma_pos_of_zero_nu_unbounded
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original deterministic cells have quadratic centred-square variance of
order the square of the physical mesh length. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (σ : ℕ → Ω → ℝ≥0)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k (ρ : Ω → ℝ≥0)
      (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
      (hρle : ∀ ω, ρ ω ≤ σ k ω)
      (δ : ℝ) (hδ : 0 < δ)
      (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω → δ ≤ riskProcess X x D t ω)
      (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
    ∀ (j : ℕ),
      let U : ℕ → ℕ → Ω → ℝ := fun m i ω =>
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
        H i ω * (Z i ω ^ 2 - (Δ : ℝ) * X.σ ^ 2)
      ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, ∀ i ∈ Finset.range (m + 1),
        Integrable (fun ω => (U m i ω) ^ 2) P ∧
          (∫ ω, (U m i ω) ^ 2 ∂P) ≤
            K / (((m + 1 : ℕ) : ℝ) ^ 2) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro k ρ hρstop hρle δ hδ hFloor A hA j
  let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
  let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
  let a : ℝ := δ / 2
  let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  let Y : ℕ → ℕ → Ω → ℝ := fun m i ω => x + X.X (s m i) ω - rightLimit D (s m i) ω
  let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    X.X (s m i + Δ m) ω - X.X (s m i) ω - (Δ m : ℝ) * X.c
  let H : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    if s m i < ρ ω then (1 / 2 : ℝ) *
      Real.exp (-(q * (s m i : ℝ))) *
      (if Y m i ω ∈ Icc a b then iteratedDeriv 2 w (Y m i ω) else 0)
    else 0
  let U : ℕ → ℕ → Ω → ℝ := fun m i ω => H m i ω * (Z m i ω ^ 2 - (Δ m : ℝ) * X.σ ^ 2)
  change ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, ∀ i ∈ Finset.range (m + 1),
    Integrable (fun ω => (U m i ω) ^ 2) P ∧
      (∫ ω, (U m i ω) ^ 2 ∂P) ≤
        K / (((m + 1 : ℕ) : ℝ) ^ 2)
  have hσ : 0 < X.σ := avram_gauss_endpoint_sigma_pos_of_zero_nu_unbounded X hν hBV
  obtain ⟨hOpen, hBand⟩ := avram_gb43_finitecap_compact_interior_band C hC hFiniteCap δ hδ j
  obtain ⟨KH, hKH, hHbound⟩ :=
    avram_gb40_original_bounded_hessian_stopped_weight
      X hBV hν q (le_of_lt hq) w C hw_smooth hOpen
      a b hBand ρ hρstop
  have hXm (t : ℝ≥0) : Measurable (X.X t) :=
    ((X.adapted t).mono (𝓕.le_rightCont t) le_rfl).mono
      (𝓕.rightCont.le t) le_rfl
  have hΔ (m : ℕ) :
      (Δ m : ℝ) = (n : ℝ) / ((m + 1 : ℕ) : ℝ) := by
    simp [Δ]
  have hCell (m i : ℕ) :
      Integrable (fun ω => (U m i ω) ^ 2) P ∧
      (∫ ω, (U m i ω) ^ 2 ∂P) ≤
        8 * KH ^ 2 * X.σ ^ 4 * (Δ m : ℝ) ^ 2 := by
    have hYm : Measurable[𝓕.rightCont (s m i)] (Y m i) := by
      have hXadapt :=
        (X.adapted (s m i)).mono (𝓕.le_rightCont (s m i)) le_rfl
      have hDadapt :=
        (dividendStrategy_rightLimit_adapted_rightCont D hD.1.1) (s m i)
      exact (measurable_const.add hXadapt).sub hDadapt
    have hHpair := hHbound (s m i) (Y m i) hYm
    have hHmeas : Measurable (H m i) := hHpair.1
    have hHb : ∀ ω, |H m i ω| ≤ KH := hHpair.2
    have hZm : Measurable (Z m i) := by
      exact ((hXm (s m i + Δ m)).sub (hXm (s m i))).sub measurable_const
    have hNorm : Measurable (fun ω : Ω =>
        (X.X ((s m i + Δ m) - s m i) ω -
          (((s m i + Δ m - s m i : ℝ≥0) : ℝ)) * X.c) / X.σ) := by
      exact ((hXm ((s m i + Δ m) - s m i)).sub measurable_const).div_const X.σ
    have hInterval : s m i ≤ s m i + Δ m := le_add_of_nonneg_right bot_le
    have hFourth : (∫⁻ ω, ENNReal.ofReal
        ((Z m i ω / X.σ) ^ 4) ∂P) ≤
        ENNReal.ofReal (3 * (Δ m : ℝ) ^ 2) := by
      simpa only [Z, add_tsub_cancel_left] using
        (avram_ubv_gauss13_localise_original_general_interval_fourth_moment_le_three_dt_sq
          X hν hσ (s m i) (s m i + Δ m) hInterval hNorm)
    have hEnergy :=
      avram_gb42_bounded_original_gaussian_quadratic_cell
        P (H m i) (Z m i) X.σ (Δ m : ℝ) KH
        hσ hKH hHmeas hHb hZm hFourth
    simpa only [U] using hEnergy
  refine ⟨8 * KH ^ 2 * X.σ ^ 4 * (n : ℝ) ^ 2,
    by positivity, ?_⟩
  intro m i hi
  obtain ⟨hI, hB⟩ := hCell m i
  refine ⟨hI, ?_⟩
  calc
    (∫ ω, (U m i ω) ^ 2 ∂P) ≤
        8 * KH ^ 2 * X.σ ^ 4 * (Δ m : ℝ) ^ 2 := hB
    _ = (8 * KH ^ 2 * X.σ ^ 4 * (n : ℝ) ^ 2) /
        (((m + 1 : ℕ) : ℝ) ^ 2) := by
          rw [hΔ m]
          have hm : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
          field_simp [ne_of_gt hm]
          <;> ring
