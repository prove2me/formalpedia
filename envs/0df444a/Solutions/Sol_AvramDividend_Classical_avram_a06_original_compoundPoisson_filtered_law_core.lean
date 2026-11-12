-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_compoundPoisson_filtered_law_core
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T18:38:19.7506+00:00
-- url     : https://prove2.me/submissions/281c93b4-8c29-4056-a3de-e0db4ec64500

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_negative_mark_measure_facts
import Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_negative_mark_bv_moments
import Theorems.Thm_AvramDividend_Classical_avram_a06_compoundPoisson_exp_integrable
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_compoundPoisson_path_increment_certificate
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_compoundPoisson_laplace_identity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
noncomputable section

/-- Assemble the original stochastic process record from a genuine
all-path increment certificate and the exact independent Laplace law. -/
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∃ (𝓕 : Filtration ℝ≥0
      (inferInstance : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))))
      (X : SpectrallyNegativeLevy P 𝓕),
        X.σ = 0 ∧
        X.ν = ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) ∧
        X.c = (1 : ℝ) +
          (∫ y in Ioo (-1 : ℝ) 0,
            y ∂((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))) ∧
        (∀ t : ℝ≥0,
          X.X t =ᵐ[P] LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ)) := by
  obtain ⟨𝓕, Z, hzero, hright, hleft, hdown, hadapt, hindep, hstationary, hLaw⟩ :=
    AvramDividend.Classical.avram_a06_original_compoundPoisson_path_increment_certificate
      P τ Y hd
  let ν : Measure ℝ := (volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)
  let c : ℝ := 1 + ∫ y in Ioo (-1 : ℝ) 0, y ∂ν
  let X : SpectrallyNegativeLevy P 𝓕 :=
    { X := Z
      c := c
      σ := 0
      ν := ν
      isProbability := inferInstance
      σ_nonneg := by norm_num
      ν_Ici := by
        exact AvramDividend.Classical.avram_a06_uniform_negative_mark_measure_facts.1
      ν_integrable := by
        exact AvramDividend.Classical.avram_a06_uniform_negative_mark_bv_moments.1
      X_zero := hzero
      rightCont := hright
      leftLim := hleft
      noPosJumps := hdown
      adapted := hadapt
      indepIncrements := hindep
      stationaryIncrements := hstationary
      laplace := by
        intro t θ hθ
        have heq :
            (fun ω => Real.exp (θ * Z t ω)) =ᵐ[P]
              (fun ω => Real.exp (θ *
                LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ) ω)) := by
          filter_upwards [hLaw t] with ω hω
          rw [hω]
        have hi :=
          AvramDividend.Classical.avram_a06_compoundPoisson_exp_integrable
            hd (t : ℝ) θ hθ
        refine ⟨hi.congr heq.symm, ?_⟩
        calc
          (∫ ω, Real.exp (θ * Z t ω) ∂P) =
            (∫ ω, Real.exp (θ *
              LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ) ω) ∂P) :=
                integral_congr_ae heq
          _ = Real.exp ((t : ℝ) * laplaceExponent c 0 ν θ) := by
            simpa only [c, ν] using
              (AvramDividend.Classical.avram_a06_original_compoundPoisson_laplace_identity
                P τ Y hd t θ hθ) }
  refine ⟨𝓕, X, rfl, rfl, rfl, ?_⟩
  exact hLaw
