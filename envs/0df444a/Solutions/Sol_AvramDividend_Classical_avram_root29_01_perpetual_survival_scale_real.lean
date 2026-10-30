-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_perpetual_survival_scale_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:15:27.494968+00:00
-- url     : https://prove2.me/submissions/1ac50d2c-f728-4f6f-8a62-0724dd50faad

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_integrator_new_genuine_perpetual_cdf_scale_all_real
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_unit_interval

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The authentic all-real Esscher perpetual survival infimum equals the real
scale-function expression; this is the missing ENNReal-to-real bridge. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ m : ℝ, 0 < m ∧
      ∀ x : ℝ,
      (⨅ t : ℝ≥0, ∫ ω,
        ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => Real.exp (φ * X.X t ω -
            (t : ℝ) * laplaceExponent X.c X.σ X.ν φ)) ω ∂P) =
      m * Real.exp (-(φ * x)) * W x := by
  obtain ⟨ν, m, hprob, hm, hCDF, hScale⟩ :=
    avram_ws01e_integrator_new_genuine_perpetual_cdf_scale_all_real
      X q φ hq hφ hroot W hW
  refine ⟨m, hm, ?_⟩
  intro x
  let F : ℝ≥0 → ℝ := fun t =>
    ∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
      (fun ω => Real.exp (φ * X.X t ω -
        (t : ℝ) * laplaceExponent X.c X.σ X.ν φ)) ω ∂P
  have hFnonneg (t : ℝ≥0) : 0 ≤ F t :=
    (esscher_weighted_lower_survival_mass_unit_interval X φ hφ.le x t).1
  have hInfNonneg : 0 ≤ (⨅ t : ℝ≥0, F t) :=
    le_ciInf hFnonneg
  have hWnn : 0 ≤ W x := by
    rcases hW with ⟨hneg, hnonneg, _, _, _⟩
    by_cases hx : x < 0
    · rw [hneg x hx]
    · exact hnonneg x (le_of_not_gt hx)
  have hScaledNonneg : 0 ≤ m * Real.exp (-(φ * x)) * W x :=
    mul_nonneg (mul_nonneg hm.le (Real.exp_pos _).le) hWnn
  have hENN :
      ENNReal.ofReal (⨅ t : ℝ≥0, F t) =
        ENNReal.ofReal (m * Real.exp (-(φ * x)) * W x) := by
    calc
      ENNReal.ofReal (⨅ t : ℝ≥0, F t) =
          ⨅ t : ℝ≥0, ENNReal.ofReal (F t) :=
        ENNReal.ofReal_iInf F
      _ = ν (Iic x) := (hCDF x).symm
      _ = _ := hScale x
  exact (ENNReal.ofReal_eq_ofReal_iff hInfNonneg hScaledNonneg).mp hENN
