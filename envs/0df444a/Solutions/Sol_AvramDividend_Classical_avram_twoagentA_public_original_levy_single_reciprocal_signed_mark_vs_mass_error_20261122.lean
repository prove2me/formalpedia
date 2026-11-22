-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_public_original_levy_single_reciprocal_signed_mark_vs_mass_error_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:09:04.725461+00:00
-- url     : https://prove2.me/submissions/5f8167ef-8383-432e-b7f8-6b9b6763a211

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_shared_negative_mark_quadratic_pointwise
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    (ν : Measure ℝ) (i : ℕ)
    (hFin : ν (Ioc (-(1 / ((i : ℝ) + 1)))
                      (-(1 / ((i : ℝ) + 2)))) < ⊤)
    (hInt : IntegrableOn (fun z : ℝ => z)
      (Ioc (-(1 / ((i : ℝ) + 1)))
           (-(1 / ((i : ℝ) + 2)))) ν) :
    let B : Set ℝ :=
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
    let c : ℝ := -(1 / ((i : ℝ) + 1))
    let δ : ℝ := 1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)
    |(∫ z in B, z ∂ν) - c * (ν B).toReal| ≤ δ * (ν B).toReal := by
  classical
  let B : Set ℝ :=
    Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
  let c : ℝ := -(1 / ((i : ℝ) + 1))
  let δ : ℝ := 1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)
  change |(∫ z in B, z ∂ν) - c * (ν B).toReal| ≤ δ * (ν B).toReal
  have hBm : MeasurableSet B := measurableSet_Ioc
  haveI : IsFiniteMeasure (ν.restrict B) :=
    ⟨by simpa [B] using hFin⟩
  have hI : Integrable (fun z : ℝ => z) (ν.restrict B) := hInt
  have hAE : ∀ᵐ z ∂(ν.restrict B), c ≤ z ∧ z ≤ c + δ := by
    filter_upwards [ae_restrict_mem hBm] with z hz
    obtain ⟨hlo, hhi, _, _⟩ :=
      avram_twoagentA_shared_negative_mark_quadratic_pointwise
        i z hz
    dsimp [c, δ]
    constructor <;> linarith
  have hLo :
      (∫ z : ℝ, c ∂(ν.restrict B)) ≤
        (∫ z : ℝ, z ∂(ν.restrict B)) :=
    integral_mono_ae (integrable_const c) hI (hAE.mono fun z hz => hz.1)
  have hHi :
      (∫ z : ℝ, z ∂(ν.restrict B)) ≤
        (∫ z : ℝ, c + δ ∂(ν.restrict B)) :=
    integral_mono_ae hI (integrable_const (c + δ))
      (hAE.mono fun z hz => hz.2)
  simp [integral_const, Measure.real, hBm] at hLo hHi
  rw [abs_of_nonneg (by nlinarith [hLo])]
  nlinarith [hHi]
