-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite13_original_stopped_gaussian_expected_quadratic_bracket
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T13:31:17.259342+00:00
-- url     : https://prove2.me/submissions/028c1c32-4575-4cc7-aeec-7ff70dad394e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite13_original_bounded_stopped_gaussian_L2_integrability
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite13_original_stopped_gaussian_increment_second_moment_difference
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite13_original_stopped_gaussian_compensated_square_mean
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite13_original_stopped_gaussian_Q_pointwise_decomposition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- The original Gaussian stopped increment has expected squared magnitude
equal to the expected increment of its sampled quadratic-variation clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (grid : ℕ → ℝ≥0) (hgrid : Monotone grid)
    (𝓖 : Filtration ℕ mΩ) [SigmaFiniteFiltration P 𝓖]
    (h𝓖 : 𝓖 =
      ({ seq := fun i : ℕ => 𝓕.rightCont (grid i)
         mono' := by
           intro i j hij
           exact 𝓕.rightCont.mono (hgrid hij)
         le' := by
           intro i
           exact 𝓕.rightCont.le (grid i) } : Filtration ℕ mΩ))
    (α β : Ω → WithTop ℕ)
    (hα : IsStoppingTime 𝓖 α) (hβ : IsStoppingTime 𝓖 β)
    (hαβ : α ≤ β)
    (N : ℕ) (hbounded : ∀ ω, β ω ≤ (N : WithTop ℕ)) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω => X.X t ω - (t : ℝ) * X.c
    let A := stoppedValue (fun i : ℕ => M (grid i)) α
    let B := stoppedValue (fun i : ℕ => M (grid i)) β
    let TA := stoppedValue (fun i : ℕ => fun _ : Ω => (grid i : ℝ) * X.σ ^ 2) α
    let TB := stoppedValue (fun i : ℕ => fun _ : Ω => (grid i : ℝ) * X.σ ^ 2) β
    (∫ ω, (B ω - A ω)^2 ∂P) = (∫ ω, TB ω ∂P) - (∫ ω, TA ω ∂P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let M : ℝ≥0 → Ω → ℝ := fun t ω => X.X t ω - (t : ℝ) * X.c
  let Q : ℝ≥0 → Ω → ℝ := fun t ω => M t ω ^ 2 - (t : ℝ) * X.σ ^ 2
  let A := stoppedValue (fun i : ℕ => M (grid i)) α
  let B := stoppedValue (fun i : ℕ => M (grid i)) β
  let TA := stoppedValue (fun i : ℕ => fun _ : Ω => (grid i : ℝ) * X.σ ^ 2) α
  let TB := stoppedValue (fun i : ℕ => fun _ : Ω => (grid i : ℝ) * X.σ ^ 2) β
  change (∫ ω, (B ω - A ω)^2 ∂P) = (∫ ω, TB ω ∂P) - (∫ ω, TA ω ∂P)
  obtain ⟨hA2, hB2, _, _⟩ :=
    avram_ubv_finite13_original_bounded_stopped_gaussian_L2_integrability
      X hν grid hgrid 𝓖 h𝓖 α β hα hβ hαβ N hbounded
  have hAI : Integrable (fun ω => A ω ^ 2) P := hA2.integrable_sq
  have hBI : Integrable (fun ω => B ω ^ 2) P := hB2.integrable_sq
  have hTA : Integrable TA P := by
    apply integrable_stoppedValue ℕ hα
    · intro i
      exact integrable_const _
    · intro ω
      exact le_trans (hαβ ω) (hbounded ω)
  have hTB : Integrable TB P := by
    apply integrable_stoppedValue ℕ hβ
    · intro i
      exact integrable_const _
    · exact hbounded
  have hQα : stoppedValue (fun i : ℕ => Q (grid i)) α =
      (fun ω => A ω ^ 2 - TA ω) :=
    avram_ubv_finite13_original_stopped_gaussian_Q_pointwise_decomposition X grid α
  have hQβ : stoppedValue (fun i : ℕ => Q (grid i)) β =
      (fun ω => B ω ^ 2 - TB ω) :=
    avram_ubv_finite13_original_stopped_gaussian_Q_pointwise_decomposition X grid β
  have hQ : (∫ ω, A ω ^ 2 - TA ω ∂P) =
      (∫ ω, B ω ^ 2 - TB ω ∂P) := by
    rw [← hQα, ← hQβ]
    exact avram_ubv_finite13_original_stopped_gaussian_compensated_square_mean
      X hν grid hgrid 𝓖 h𝓖 α β hα hβ hαβ N hbounded
  have hMom : (∫ ω, B ω ^ 2 ∂P) - (∫ ω, A ω ^ 2 ∂P) =
      (∫ ω, TB ω ∂P) - (∫ ω, TA ω ∂P) := by
    rw [integral_sub hAI hTA, integral_sub hBI hTB] at hQ
    linarith
  calc
    (∫ ω, (B ω - A ω)^2 ∂P) =
        (∫ ω, B ω ^ 2 ∂P) - (∫ ω, A ω ^ 2 ∂P) :=
      avram_ubv_finite13_original_stopped_gaussian_increment_second_moment_difference
        X hν grid hgrid 𝓖 h𝓖 α β hα hβ hαβ N hbounded
    _ = (∫ ω, TB ω ∂P) - (∫ ω, TA ω ∂P) := hMom
