-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsv_original_finitecap_interior_gaussian_prepost_expected_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T23:01:13.380801+00:00
-- url     : https://prove2.me/submissions/b5236896-6b1a-420d-b618-627247751833

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_lsv_original_finitecap_interior_gaussian_prepost_ae_domination
import Theorems.Thm_AvramDividend_Classical_avram_lsv_original_preruin_discounted_gaussian_full_grid_sqrt_rate
import Theorems.Thm_AvramDividend_Classical_avram_lsv_original_physical_prepost_gradient_gaussian_mesh_measurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) (hρle : ∀ ω, ρ ω ≤ τ ω)
    (j : ℕ) (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1))
    (hpost : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t < ρ ω →
      x + X.X t ω - rightLimit D t ω ∈
        Icc ((1 : ℝ) / ((j : ℝ) + 1)) (x + ((j : ℝ) + 1)))
    (hBandCap : ENNReal.ofReal (x + ((j : ℝ) + 1)) < C) :
    let Elinear : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let Z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
        let U := Z ^ 2 - (Δ : ℝ) * X.σ ^ 2
        let ypost := x + X.X s ω - rightLimit D s ω
        let ypre := riskProcess X x D s ω
        let e : ℝ := if s < ρ ω then Real.exp (-(q * (s : ℝ))) else 0
        |e| * |deriv w ypost - deriv w ypre| * |Z|
    let V : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let H : ℝ := if s < ρ ω then
          Real.exp (-(q * (s : ℝ))) *
            (rightLimit D s ω - D s ω)
          else 0
        let Z : ℝ := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
        H * |Z|
    ∃ L : ℝ, 0 ≤ L ∧ ∀ m : ℕ,
      Integrable (Elinear m) P ∧
        (∫ ω, Elinear m ω ∂P) ≤
          L * (∫ ω, V m ω ∂P) := by
  classical
  intro Elinear V
  have hσnn : 0 ≤ X.σ := X.σ_nonneg
  have hσ : 0 < X.σ := lt_of_le_of_ne hσnn (Ne.symm hSigmaNonzero)
  have hRuin (ω : Ω) : (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω := by
    calc
      (ρ ω : ℝ≥0∞) ≤ (τ ω : ℝ≥0∞) := by exact_mod_cast hρle ω
      _ = min (ruinTime X x D ω) (n : ℝ≥0∞) := by
        rw [hτeq ω]
        exact ENNReal.coe_toNNReal (by simp)
      _ ≤ ruinTime X x D ω := min_le_left _ _
  obtain ⟨L,hL,hPath⟩ :=
    avram_lsv_original_finitecap_interior_gaussian_prepost_ae_domination
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hFiniteCap
      hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad x hx hxc D hD
      hw_nonneg hjump n hn τ hτeq hτstop ρ hρstop hρle j hprefix hpost hBandCap
  obtain ⟨KV,hKV,hVI,hVR⟩ :=
    avram_lsv_original_preruin_discounted_gaussian_full_grid_sqrt_rate
      X hNuZero hBV hσ x (le_of_lt hx) D hD.1.1 n hn
      ρ hρstop hRuin q (le_of_lt hq)
  have hEM (m : ℕ) : Measurable (Elinear m) :=
    avram_lsv_original_physical_prepost_gradient_gaussian_mesh_measurable
      X w x D hD.1.1 q n ρ hρstop m
  refine ⟨L,hL,?_⟩
  intro m
  have hIM : Integrable (fun ω => L * V m ω) P := (hVI m).const_mul L
  have hNonneg : ∀ᵐ ω ∂P, 0 ≤ Elinear m ω :=
    hPath.mono (fun ω hw => (hw m).1)
  have hLe : ∀ᵐ ω ∂P, Elinear m ω ≤ L * V m ω :=
    hPath.mono (fun ω hw => (hw m).2)
  have hDom : Integrable (Elinear m) P := by
    apply hIM.mono' (hEM m).aestronglyMeasurable
    filter_upwards [hNonneg,hLe] with ω h0 hle
    have hb : 0 ≤ L * V m ω := le_trans h0 hle
    simpa only [Real.norm_eq_abs,abs_of_nonneg h0,abs_of_nonneg hb] using hle
  refine ⟨hDom,?_⟩
  calc
    (∫ ω, Elinear m ω ∂P) ≤ (∫ ω, L * V m ω ∂P) :=
      integral_mono_ae hDom hIM hLe
    _ = L * (∫ ω, V m ω ∂P) := integral_const_mul _ _
