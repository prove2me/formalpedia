-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb74_original_linear_diagonal_variance_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T01:16:01.401812+00:00
-- url     : https://prove2.me/submissions/f74fdec4-beab-45ed-bda5-f4ee93d37413

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB57_original_finitecap_linear_grid_cell_memLp_two
import Theorems.Thm_AvramDividend_Classical_avram_gb54_original_finitecap_linear_grid_diagonal_L2_cauchy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian15_real_squared_energy_to_L2_cauchy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (σ : ℕ → Ω → ℝ≥0)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω) : ∀ k (ρ : Ω → ℝ≥0) (hρstop : IsStoppingTime 𝓕.rightCont
        (fun ω => (ρ ω : WithTop ℝ≥0))) (hρle : ∀ ω, ρ ω ≤ σ k ω) (δ : ℝ) (hδ : 0 < δ)
      (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω → δ ≤ riskProcess X x D t ω)
      (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A → ∀ (j : ℕ),
      let L : ℕ → Ω → ℝ := fun m ω =>
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
        let a : ℝ := δ / 2
        let b : ℝ := C.toReal *
          (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        let Y : ℕ → Ω → ℝ := fun i η =>
          x + X.X (s i) η - rightLimit D (s i) η
        let Z : ℕ → Ω → ℝ := fun i η =>
          X.X (s i + Δ) η - X.X (s i) η - (Δ : ℝ) * X.c
        let G : ℕ → Ω → ℝ := fun i η =>
          if s i < ρ η then Real.exp (-(q * (s i : ℝ))) *
            (if Y i η ∈ Icc a b then deriv w (Y i η) else 1) else 0
        let H : ℕ → Ω → ℝ := fun i η =>
          if s i < ρ η then (1 / 2 : ℝ) * Real.exp (-(q * (s i : ℝ))) *
            (if Y i η ∈ Icc a b then iteratedDeriv 2 w (Y i η) else 0) else 0
        (Finset.range (m + 1)).sum (fun i => G i ω * Z i ω)
      ∃ v : ℝ, Tendsto (fun m : ℕ => ∫ ω, (L m ω) ^ 2 ∂P) atTop (𝓝 v) := by
  intro k ρ hρstop hρle δ hδ hFloor A hA j L
  change ∃ v : ℝ, Tendsto (fun m => ∫ ω, (L m ω)^2 ∂P) atTop (𝓝 v)
  have hLp (m : ℕ) : MemLp (L m) 2 P := by
    dsimp only [L]
    apply memLp_finset_sum (Finset.range (m + 1))
    intro i hi
    simpa using (avram_gbB57_original_finitecap_linear_grid_cell_memLp_two
      X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad x hx hxc D
        hD hw_nonneg hjump n hn τ hτeq hτmeas hτstop σ hσstop hσle k ρ hρstop hρle δ hδ hFloor A
        hA j m i hi)
  have hEnergy : Tendsto (fun nm : ℕ × ℕ =>
      ∫ ω, (L nm.1 ω - L nm.2 ω)^2 ∂P) atTop (𝓝 (0 : ℝ)) := by
    simpa only [L] using
      (avram_gb54_original_finitecap_linear_grid_diagonal_L2_cauchy
        X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad x hx hxc D
          hD hw_nonneg hjump n hn τ hτeq hτmeas hτstop σ hσstop hσle k ρ hρstop hρle δ hδ hFloor
          A hA j)
  have hPair : ∀ m l : ℕ, MemLp (L m - L l) 2 P := by
    intro m l
    exact (hLp m).sub (hLp l)
  have hElp : Tendsto (fun nm : ℕ × ℕ =>
      eLpNorm (L nm.1 - L nm.2) 2 P) atTop (𝓝 0) :=
    avram_ubv_gaussian15_real_squared_energy_to_L2_cauchy P L hPair hEnergy
  let F : ℕ → Lp ℝ 2 P := fun m => MemLp.toLp (L m) (hLp m)
  have hCauchy : CauchySeq F := by
    apply (Lp.cauchySeq_Lp_iff_cauchySeq_eLpNorm F).2
    convert hElp using 1
    funext nm
    apply eLpNorm_congr_ae
    have h1 : (F nm.1).val.cast =ᵐ[P] L nm.1 := by
      simpa only [F, MemLp.toLp_val] using
        (AEEqFun.coeFn_mk (L nm.1) (hLp nm.1).1)
    have h2 : (F nm.2).val.cast =ᵐ[P] L nm.2 := by
      simpa only [F, MemLp.toLp_val] using
        (AEEqFun.coeFn_mk (L nm.2) (hLp nm.2).1)
    exact h1.sub h2
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete hCauchy
  have hNorm : Tendsto (fun m => ‖F m‖^2) atTop (𝓝 (‖u‖^2)) :=
    (tendsto_norm.comp hu).pow 2
  have hNormEq (m : ℕ) :
      ‖F m‖ = Real.sqrt (∫ ω, (L m ω)^2 ∂P) := by
    change ‖MemLp.toLp (L m) (hLp m)‖ = _
    rw [Lp.norm_toLp]
    rw [MemLp.eLpNorm_eq_integral_rpow_norm
      (by norm_num) (by norm_num) (hLp m)]
    simp [Real.sqrt_eq_rpow, Real.norm_eq_abs, sq_abs]
    all_goals
      have hInt : 0 ≤ ∫ ω, (L m ω)^2 ∂P := by
        exact integral_nonneg (Pi.le_def.mpr (fun ω => sq_nonneg (L m ω)))
      exact Real.rpow_nonneg hInt _
  have hMoment (m : ℕ) :
      (∫ ω, (L m ω)^2 ∂P) = ‖F m‖^2 := by
    rw [hNormEq]
    have hInt : 0 ≤ ∫ ω, (L m ω)^2 ∂P := by
      exact integral_nonneg (Pi.le_def.mpr (fun ω => sq_nonneg (L m ω)))
    exact (Real.sq_sqrt hInt).symm
  refine ⟨‖u‖^2, ?_⟩
  simpa only [hMoment] using hNorm
