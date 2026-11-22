-- Prove2me | solution 1 for AvramDividend.Classical.avram_agentB_original_gaussian_prepost_pure_linear_atom_rootmesh_rate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T21:47:27.480274+00:00
-- url     : https://prove2.me/submissions/fa483430-c1df-4bdc-8930-6b7681aa4cc4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_lsv_original_preruin_discounted_gaussian_full_grid_sqrt_rate
import Theorems.Thm_AvramDividend_Classical_avram_lsv_original_prepost_gradient_discounted_atom_grid_domination
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
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
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω)
    (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
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
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ m, Integrable (Elinear m) P) ∧
      ∀ m : ℕ,
        (∫ ω, Elinear m ω ∂P) ≤
          K * Real.sqrt ((n : ℝ) / ((m + 1 : ℕ) : ℝ)) := by
  intro Elinear
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
  have hσnn : 0 ≤ X.σ := X.σ_nonneg
  have hσ : 0 < X.σ := lt_of_le_of_ne hσnn (Ne.symm hSigmaNonzero)
  have hRuin (ω : Ω) :
      (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω := by
    calc
      (ρ ω : ℝ≥0∞) ≤ (τ ω : ℝ≥0∞) := by exact_mod_cast hρle ω
      _ = min (ruinTime X x D ω) (n : ℝ≥0∞) := by
        rw [hτeq ω]
        exact ENNReal.coe_toNNReal (by simp)
      _ ≤ ruinTime X x D ω := min_le_left _ _
  obtain ⟨L, hL, hDom⟩ :=
    avram_lsv_original_prepost_gradient_discounted_atom_grid_domination
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad x hx hxc D hD
      hw_nonneg hjump n hn τ hτeq hτstop ρ hρstop hρle j hprefix
  obtain ⟨K, hK, hInt, hRate⟩ :=
    avram_lsv_original_preruin_discounted_gaussian_full_grid_sqrt_rate
      X hNuZero hBV hσ x (le_of_lt hx) D hD.1.1 n hn
      ρ hρstop hRuin q (le_of_lt hq)
  refine ⟨L * K, mul_nonneg hL hK, ?_, ?_⟩
  · intro m
    exact (hDom m).1
  · intro m
    calc
      (∫ ω, Elinear m ω ∂P) ≤ L * (∫ ω, V m ω ∂P) :=
        (hDom m).2
      _ ≤ L * (K * Real.sqrt ((n : ℝ) / ((m + 1 : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left (hRate m) hL
      _ = (L * K) * Real.sqrt ((n : ℝ) / ((m + 1 : ℕ) : ℝ)) := by ring
