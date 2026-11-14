-- Prove2me | solution 2 for AvramDividend.Classical.avram_ga_a134_b0_actual_fullcell_positive_L1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:39:18.030099+00:00
-- url     : https://prove2.me/submissions/32d1d911-ece0-4e2a-9f6a-abd5ce26a4b7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a130_original_gaussian_physically_full_mesh_three_error_source_exact_sum
import Theorems.Thm_AvramDividend_Classical_avram_ga_a136_original_gaussian_fullcell_positive_three_source_errors_L1_glue
import Theorems.Thm_AvramDividend_Classical_avram_ga_a137_original_physical_fullcell_positive_Taylor_cross_discount_pointwise_bound
import Theorems.Thm_AvramDividend_Classical_avram_ga_a149_b0_true_fullcell_classical_Taylor_positive_L1
import Theorems.Thm_AvramDividend_Classical_avram_ga_a150_b0_true_fullcell_Hessian_cross_absolute_L1
import Theorems.Thm_AvramDividend_Classical_avram_ga_a151_b0_true_fullcell_discount_positive_L1
import Theorems.Thm_AvramDividend_Classical_avram_ga_a152_b0_original_fullcell_positive_residual_aestrongly_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let Full : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
    let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
    let H : ℕ → ℝ := fun i =>
      E (s i) * (deriv w (Y (s i)) * Z i +
        (iteratedDeriv 2 w (Y (s i)) / 2) *
          (Z i^2 - (Δ : ℝ) * X.σ^2)) +
        (Δ : ℝ) * E (s i) * X.generator w (Y (s i))
    let F : ℕ → ℝ := fun i =>
      E (s i + Δ) * (w (Y (s i) + R i) - w (Y (s i))) - H i
    ∑ i ∈ Finset.range m,
      if s i < ρ ω ∧ s i + Δ ≤ ρ ω then F i else 0
    (∀ m, Integrable (fun ω => max (Full m ω) 0) P) ∧
    Tendsto (fun m => ∫ ω, max (Full m ω) 0 ∂P) atTop (nhds (0 : ℝ)) := by
  classical
  let Full : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1); let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ; let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ))); let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω; let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω; let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c; let H : ℕ → ℝ := fun i => E (s i) * (deriv w (Y (s i)) * Z i + (iteratedDeriv 2 w (Y (s i)) / 2) * (Z i^2 - (Δ : ℝ) * X.σ^2)) + (Δ : ℝ) * E (s i) * X.generator w (Y (s i)); let F : ℕ → ℝ := fun i => E (s i + Δ) * (w (Y (s i) + R i) - w (Y (s i))) - H i; ∑ i ∈ Finset.range m, if s i < ρ ω ∧ s i + Δ ≤ ρ ω then F i else 0
  let T : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1); let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ; let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ))); let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω; let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω; let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c; ∑ i ∈ Finset.range m, if s i < ρ ω ∧ s i + Δ ≤ ρ ω then E (s i) * (w (Y (s i) + R i) - w (Y (s i)) - deriv w (Y (s i)) * R i - (iteratedDeriv 2 w (Y (s i)) / 2) * R i^2) else 0
  let B : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1); let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ; let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ))); let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω; let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω; let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c; ∑ i ∈ Finset.range m, if s i < ρ ω ∧ s i + Δ ≤ ρ ω then E (s i) * (iteratedDeriv 2 w (Y (s i)) / 2) * (R i^2 - Z i^2) else 0
  let Cerr : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1); let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ; let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ))); let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω; let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω; let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c; ∑ i ∈ Finset.range m, if s i < ρ ω ∧ s i + Δ ≤ ρ ω then (E (s i + Δ) - E (s i)) * (w (Y (s i) + R i) - w (Y (s i))) else 0
  have hT :=
    avram_ga_a149_b0_true_fullcell_classical_Taylor_positive_L1
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix
  have hB :=
    avram_ga_a150_b0_true_fullcell_Hessian_cross_absolute_L1
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix
  have hCerr :=
    avram_ga_a151_b0_true_fullcell_discount_positive_L1
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix
  have hM :=
    avram_ga_a152_b0_original_fullcell_positive_residual_aestrongly_measurable
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix

  have hSplit (m : ℕ) (ω : Ω) :
      Full m ω = T m ω + B m ω + Cerr m ω := by
    exact avram_ga_a130_original_gaussian_physically_full_mesh_three_error_source_exact_sum
      X hNuZero x D w q ω n m (ρ ω)
  have hFI : ∀ m, Integrable (fun ω => max (Full m ω) 0) P := by
    intro m
    refine Integrable.mono' (((hT.1 m).add (hB.1 m)).add (hCerr.1 m))
      (hM m) (Filter.Eventually.of_forall ?_)
    intro ω
    change ‖max (Full m ω) 0‖ ≤
      (max (T m ω) 0 + |B m ω|) + max (Cerr m ω) 0
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact avram_ga_a137_original_physical_fullcell_positive_Taylor_cross_discount_pointwise_bound
      X hNuZero x D w q ω n m (ρ ω)
  exact ⟨hFI,
    avram_ga_a136_original_gaussian_fullcell_positive_three_source_errors_L1_glue
      P Full T B Cerr hSplit hFI hT.1 hB.1 hCerr.1
      hT.2 hB.2 hCerr.2⟩
