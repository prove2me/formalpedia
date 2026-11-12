-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb52_chronological_original_quadratic_cells_cross_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T11:44:01.482162+00:00
-- url     : https://prove2.me/submissions/d91a096c-2ed5-404f-a201-15fd5fdcddf6

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gb49_predictable_real_condExp_cross_zero
import Theorems.Thm_AvramDividend_Classical_avram_gb50_predictable_stopped_hessian_adapted
import Theorems.Thm_AvramDividend_Classical_avram_gb51_integrable_product_of_integrable_squares
import Theorems.Thm_AvramDividend_Classical_avram_gb34_original_finitecap_quadratic_cell_fourth_bound
import Theorems.Thm_AvramDividend_Classical_avram_gb43_finitecap_compact_interior_band
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_deterministic_quadratic_residual_condExp_zero
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

/-- Ordered original quadratic Gaussian cells are orthogonal by the
right-continuous filtration conditional-centred-square identity. -/
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
      (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
        δ ≤ riskProcess X x D t ω)
      (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
    ∀ (j : ℕ),
      let U : ℕ → ℕ → Ω → ℝ := fun m i ω =>
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
        let a : ℝ := δ / 2
        let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        let Y : ℕ → Ω → ℝ := fun i η => x + X.X (s i) η - rightLimit D (s i) η
        let Z : ℕ → Ω → ℝ := fun i η => X.X (s i + Δ) η - X.X (s i) η - (Δ : ℝ) * X.c
        let H : ℕ → Ω → ℝ := fun i η =>
          if s i < ρ η then (1 / 2 : ℝ) *
            Real.exp (-(q * (s i : ℝ))) *
            (if Y i η ∈ Icc a b then iteratedDeriv 2 w (Y i η) else 0)
          else 0
        H i ω * (Z i ω ^ 2 - (Δ : ℝ) * X.σ ^ 2)
      ∀ m : ℕ, ∀ i ∈ Finset.range (m + 1), ∀ r ∈ Finset.range (m + 1),
        i < r →
          Integrable (fun ω => U m i ω * U m r ω) P ∧
            (∫ ω, U m i ω * U m r ω ∂P) = 0 := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro k ρ hρstop hρle δ hδ hFloor A hA j
  let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
  let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
  let a : ℝ := δ / 2
  let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  let Y : ℕ → ℕ → Ω → ℝ := fun m i ω => x + X.X (s m i) ω - rightLimit D (s m i) ω
  let Z : ℕ → ℕ → Ω → ℝ := fun m i ω => X.X (s m i + Δ m) ω - X.X (s m i) ω - (Δ m : ℝ) * X.c
  let H : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    if s m i < ρ ω then (1 / 2 : ℝ) *
      Real.exp (-(q * (s m i : ℝ))) *
      (if Y m i ω ∈ Icc a b then iteratedDeriv 2 w (Y m i ω) else 0)
    else 0
  let U : ℕ → ℕ → Ω → ℝ := fun m i ω => H m i ω * (Z m i ω ^ 2 - (Δ m : ℝ) * X.σ ^ 2)
  change ∀ m : ℕ, ∀ i ∈ Finset.range (m + 1),
    ∀ r ∈ Finset.range (m + 1), i < r →
      Integrable (fun ω => U m i ω * U m r ω) P ∧
        (∫ ω, U m i ω * U m r ω ∂P) = 0
  obtain ⟨hOpen, hBand⟩ := avram_gb43_finitecap_compact_interior_band C hC hFiniteCap δ hδ j
  obtain ⟨KH, hKH, hHadapt⟩ :=
    avram_gb50_predictable_stopped_hessian_adapted
      X hBV hν q (le_of_lt hq) w C hw_smooth hOpen a b hBand ρ hρstop
  obtain ⟨K, hK, hSquare⟩ :=
    avram_gb34_original_finitecap_quadratic_cell_fourth_bound
      X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont
      hw_neg hw_smooth hw_gen hw_grad x hx hxc D hD
      hw_nonneg hjump n hn τ hτeq hτmeas hτstop σ hσstop hσle
      k ρ hρstop hρle δ hδ hFloor A hA j
  have hXm (t : ℝ≥0) : Measurable[𝓕.rightCont t] (X.X t) :=
    (X.adapted t).mono (𝓕.le_rightCont t) le_rfl
  have hYm (m i : ℕ) : Measurable[𝓕.rightCont (s m i)] (Y m i) := by
    exact (measurable_const.add (hXm (s m i))).sub
      ((dividendStrategy_rightLimit_adapted_rightCont D hD.1.1) (s m i))
  have hHm (m i : ℕ) : Measurable[𝓕.rightCont (s m i)] (H m i) :=
    (hHadapt (s m i) (Y m i) (hYm m i)).1
  have hUm (m i : ℕ) : Measurable[𝓕.rightCont (s m i + Δ m)] (U m i) := by
    have hle : s m i ≤ s m i + Δ m := le_add_of_nonneg_right bot_le
    have hZ : Measurable[𝓕.rightCont (s m i + Δ m)] (Z m i) :=
      ((hXm (s m i + Δ m)).sub
        ((hXm (s m i)).mono (𝓕.rightCont.mono hle) le_rfl)).sub measurable_const
    exact ((hHm m i).mono (𝓕.rightCont.mono hle) le_rfl).mul
      ((hZ.pow_const 2).sub measurable_const)
  have hUg (m i : ℕ) : Measurable (U m i) :=
    (hUm m i).mono (𝓕.rightCont.le (s m i + Δ m)) le_rfl
  intro m i hi r hr hir
  have hCross : Integrable (fun ω => U m i ω * U m r ω) P := avram_gb51_integrable_product_of_integrable_squares P
      (U m i) (U m r) (hUg m i) (hUg m r)
      (hSquare m i hi).1 (hSquare m r hr).1
  have hnext (v : ℕ) : s m v + Δ m = s m (v + 1) := by simp [s, add_mul]
  have htime : s m i + Δ m ≤ s m r := by
    rw [hnext]
    have hnatr : ((i + 1 : ℕ) : ℝ≥0) ≤ (r : ℝ≥0) := by
      exact_mod_cast (Nat.succ_le_of_lt hir)
    exact mul_le_mul_of_nonneg_right hnatr bot_le
  have hPrev : Measurable[𝓕.rightCont (s m r)]
      (fun ω => U m i ω * H m r ω) :=
    ((hUm m i).mono (𝓕.rightCont.mono htime) le_rfl).mul (hHm m r)
  have hQ :
      Integrable (fun ω => Z m r ω ^ 2 - (Δ m : ℝ) * X.σ ^ 2) P ∧
      P[(fun ω => Z m r ω ^ 2 - (Δ m : ℝ) * X.σ ^ 2) |
        𝓕.rightCont (s m r)] =ᵐ[P] (fun _ => (0 : ℝ)) := by
    simpa [Z, add_tsub_cancel_left] using
      (avram_wave6_03_original_rightCont_gaussian_deterministic_quadratic_residual_condExp_zero
        X hν (s m r) (s m r + Δ m) (le_add_of_nonneg_right bot_le))
  have hProd : Integrable (fun ω => (U m i ω * H m r ω) * (Z m r ω ^ 2 - (Δ m : ℝ) * X.σ ^ 2)) P := by
    convert hCross using 1
    funext ω
    dsimp [U]
    ring
  have hZero := avram_gb49_predictable_real_condExp_cross_zero
    (𝓕.rightCont.le (s m r)) _ _
    hPrev hQ.1 hProd hQ.2
  refine ⟨hCross, ?_⟩
  convert hZero using 2
  funext ω
  dsimp [U]
  ring
