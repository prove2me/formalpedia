-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite13_original_stopped_gaussian_increment_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T13:05:02.331679+00:00
-- url     : https://prove2.me/submissions/7bc029e7-8265-4301-9024-7bb8fae51c5f

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite13_original_stopped_gaussian_cross_moment
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite13_original_bounded_stopped_gaussian_L2_integrability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- The later-minus-earlier original stopped Gaussian increment is L1
orthogonal to the earlier stopped value on one sampled filtration. -/
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
    (∫ ω, A ω * (B ω - A ω) ∂P) = 0 := by
  letI : IsProbabilityMeasure P := X.isProbability
  let M : ℝ≥0 → Ω → ℝ := fun t ω => X.X t ω - (t : ℝ) * X.c
  let A := stoppedValue (fun i : ℕ => M (grid i)) α
  let B := stoppedValue (fun i : ℕ => M (grid i)) β
  change (∫ ω, A ω * (B ω - A ω) ∂P) = 0
  obtain ⟨hA2, hB2, hAadapt, hABint⟩ :=
    avram_ubv_finite13_original_bounded_stopped_gaussian_L2_integrability
      X hν grid hgrid 𝓖 h𝓖 α β hα hβ hαβ N hbounded
  have hBint : Integrable B P := MemLp.integrable (by norm_num) hB2
  have hAAint : Integrable (fun ω => A ω * A ω) P := by
    convert MemLp.integrable_mul hA2 hA2 using 1 <;> rfl
  have hCross : (∫ ω, A ω * B ω ∂P) =
      (∫ ω, A ω * A ω ∂P) :=
    avram_ubv_finite13_original_stopped_gaussian_cross_moment
      X hν grid hgrid 𝓖 h𝓖 α β hα hβ hαβ N hbounded
      A B rfl rfl hAadapt hBint hABint
  calc
    (∫ ω, A ω * (B ω - A ω) ∂P) =
        (∫ ω, A ω * B ω - A ω * A ω ∂P) := by
      apply integral_congr_ae
      filter_upwards [] with ω
      ring
    _ = (∫ ω, A ω * B ω ∂P) - (∫ ω, A ω * A ω ∂P) :=
      integral_sub hABint hAAint
    _ = 0 := sub_eq_zero.mpr hCross
