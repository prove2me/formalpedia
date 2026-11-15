-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a395_true_crossing_HJB_percell_common_integrable_majorant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T17:02:11.529027+00:00
-- url     : https://prove2.me/submissions/04ff335a-7e94-47f6-b45a-be66e929a2eb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a396_original_crossing_compact_C2_generator_coefficients
import Theorems.Thm_AvramDividend_Classical_avram_ga_a397_original_fullcell_gaussian_uniform_quadratic_integrable_majorant
import Theorems.Thm_AvramDividend_Classical_avram_ga_a398_scalar_Gaussian_HJB_fullcell_absolute_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option maxHeartbeats 800000

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
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : Ω → ℝ≥0 → ℝ := fun ω t => x + X.X t ω - rightLimit D t ω
    let Hcell : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      let z := X.X (s m i + Δ m) ω - X.X (s m i) ω - (Δ m : ℝ) * X.c
      E (s m i) * (deriv w (Y ω (s m i)) * z +
        (iteratedDeriv 2 w (Y ω (s m i)) / 2) *
          (z^2 - (Δ m : ℝ) * X.σ^2)) +
        (Δ m : ℝ) * E (s m i) * X.generator w (Y ω (s m i))
    ∃ B : Ω → ℝ, Integrable B P ∧
      ∀ (m : ℕ), ∀ᵐ ω ∂P, ∀ (i : ℕ), i < m →
        s m i < ρ ω → ρ ω < s m i + Δ m →
        |Hcell m i ω| ≤ B ω := by
  classical
  intro Δ s E Y Hcell
  obtain ⟨K, hK, hCoeffs⟩ :=
    avram_ga_a396_original_crossing_compact_C2_generator_coefficients
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix
  obtain ⟨V, hVI, hV0, hVbound⟩ :=
    avram_ga_a397_original_fullcell_gaussian_uniform_quadratic_integrable_majorant
      X hNuZero n
  let a : ℝ := X.σ^2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  let C0 : ℝ := K * (2 + a)
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  let B : Ω → ℝ := fun ω => C0 * V ω
  have hBI : Integrable B P := hVI.const_mul C0
  refine ⟨B, hBI, ?_⟩
  intro m
  filter_upwards [hCoeffs, hVbound m] with ω hc hv
  intro i hi hs ht
  let z : ℝ := X.X (s m i + Δ m) ω - X.X (s m i) ω -
    (Δ m : ℝ) * X.c
  let y : ℝ := Y ω (s m i)
  have hD : 0 ≤ (Δ m : ℝ) := by exact_mod_cast (show (0 : ℝ≥0) ≤ Δ m from bot_le)
  have hs0 : 0 ≤ (s m i : ℝ) := by positivity
  have hE0 : 0 ≤ E (s m i) := Real.exp_nonneg _
  have hE1 : E (s m i) ≤ 1 := by
    dsimp [E]
    apply (Real.exp_le_one_iff).2
    nlinarith [hD]
  have hh := hc m i
  have hcoef : |deriv w y| ≤ K ∧
        |iteratedDeriv 2 w y| ≤ K ∧
        |X.generator w y| ≤ K := by
    simpa only [Y,s,Δ] using hh hs
  have hv0 : |z| + z^2 + (Δ m : ℝ) ≤ V ω := by
    simpa only [z,s,Δ] using hv i hi
  have hscalar := avram_ga_a398_scalar_Gaussian_HJB_fullcell_absolute_budget
    K a (E (s m i)) (Δ m : ℝ) z
    (deriv w y) (iteratedDeriv 2 w y)
    (X.generator w y) hK ha hE0 hE1 hD
    hcoef.1 hcoef.2.1 hcoef.2.2
  have hEq : Hcell m i ω =
      E (s m i) * (deriv w y * z +
        iteratedDeriv 2 w y / 2 * (z^2 - (Δ m : ℝ) * a)) +
        (Δ m : ℝ) * E (s m i) * X.generator w y := by
    rfl
  rw [hEq]
  exact hscalar.trans (mul_le_mul_of_nonneg_left hv0 hC0)
