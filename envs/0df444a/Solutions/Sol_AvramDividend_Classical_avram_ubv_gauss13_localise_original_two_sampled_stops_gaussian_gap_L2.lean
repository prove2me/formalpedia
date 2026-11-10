-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss13_localise_original_two_sampled_stops_gaussian_gap_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T07:51:10.650993+00:00
-- url     : https://prove2.me/submissions/5dfcb7d6-4289-489e-9970-dda704196a0c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite13_original_stopped_gaussian_expected_quadratic_bracket

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

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
    (N : ℕ) (hbounded : ∀ ω, β ω ≤ (N : WithTop ℕ))
    (ε : ℝ)
    (hTimeA : Integrable (stoppedValue
      (fun i : ℕ => fun _ : Ω => (grid i : ℝ) * X.σ ^ 2) α) P)
    (hTimeB : Integrable (stoppedValue
      (fun i : ℕ => fun _ : Ω => (grid i : ℝ) * X.σ ^ 2) β) P)
    (hGap : ∀ ω,
      stoppedValue
          (fun i : ℕ => fun _ : Ω => (grid i : ℝ) * X.σ ^ 2) β ω -
        stoppedValue
          (fun i : ℕ => fun _ : Ω => (grid i : ℝ) * X.σ ^ 2) α ω
        ≤ ε * X.σ ^ 2) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c
    let A := stoppedValue (fun i : ℕ => M (grid i)) α
    let B := stoppedValue (fun i : ℕ => M (grid i)) β
    (∫ ω, (B ω - A ω) ^ 2 ∂P) ≤ ε * X.σ ^ 2 := by
  letI : IsProbabilityMeasure P := X.isProbability
  let M : ℝ≥0 → Ω → ℝ := fun t ω =>
    X.X t ω - (t : ℝ) * X.c
  let A := stoppedValue (fun i : ℕ => M (grid i)) α
  let B := stoppedValue (fun i : ℕ => M (grid i)) β
  let TA := stoppedValue
    (fun i : ℕ => fun _ : Ω => (grid i : ℝ) * X.σ ^ 2) α
  let TB := stoppedValue
    (fun i : ℕ => fun _ : Ω => (grid i : ℝ) * X.σ ^ 2) β
  change (∫ ω, (B ω - A ω) ^ 2 ∂P) ≤ ε * X.σ ^ 2
  have hEq : (∫ ω, (B ω - A ω) ^ 2 ∂P) =
      (∫ ω, TB ω ∂P) - (∫ ω, TA ω ∂P) := by
    exact avram_ubv_finite13_original_stopped_gaussian_expected_quadratic_bracket
      X hν grid hgrid 𝓖 h𝓖 α β hα hβ hαβ N hbounded
  have hTA : Integrable TA P := hTimeA
  have hTB : Integrable TB P := hTimeB
  have hUpper : ∀ᵐ ω ∂P, TB ω - TA ω ≤ ε * X.σ ^ 2 :=
    Filter.Eventually.of_forall hGap
  calc
    (∫ ω, (B ω - A ω) ^ 2 ∂P) =
        (∫ ω, TB ω ∂P) - (∫ ω, TA ω ∂P) := hEq
    _ = ∫ ω, TB ω - TA ω ∂P := (integral_sub hTB hTA).symm
    _ ≤ ∫ _ : Ω, ε * X.σ ^ 2 ∂P :=
      integral_mono_ae (hTB.sub hTA) (integrable_const _) hUpper
    _ = ε * X.σ ^ 2 := by simp
