-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_02b_original_future_path_conditional_first_second_moments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:27:42.614698+00:00
-- url     : https://prove2.me/submissions/b3877701-7ac0-4876-a558-71d5f060c78b

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_finite_future_increment_sigma_indep_past
import Theorems.Thm_AvramDividend_Classical_chat04_whole_future_process_indep_past_of_finite_cylinders
import Theorems.Thm_AvramDividend_Classical_chat04_full_shifted_future_path_condExp_of_independence
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0)
    (J : (ℝ≥0 → ℝ) → ℝ) (hJ : Measurable J)
    (hJint : Integrable
      (fun ω => J (fun t => X.X (s + t) ω - X.X s ω)) P)
    (hJ2int : Integrable
      (fun ω => (J (fun t => X.X (s + t) ω - X.X s ω)) ^ 2) P) :
    (P[(fun ω => J (fun t => X.X (s + t) ω - X.X s ω)) | 𝓕 s] =ᵐ[P]
      (fun _ => ∫ ω, J (fun t => X.X (s + t) ω - X.X s ω) ∂P)) ∧
    (P[(fun ω => (J (fun t => X.X (s + t) ω - X.X s ω)) ^ 2) | 𝓕 s] =ᵐ[P]
      (fun _ => ∫ ω, (J (fun t => X.X (s + t) ω - X.X s ω)) ^ 2 ∂P)) := by
  have hFuture := chat04_whole_future_process_indep_past_of_finite_cylinders
    X s (finite_future_increment_sigma_indep_past X s)
  constructor
  · exact chat04_full_shifted_future_path_condExp_of_independence
      X s hFuture J hJ hJint
  · exact chat04_full_shifted_future_path_condExp_of_independence
      X s hFuture (fun x => (J x) ^ 2) (hJ.pow_const 2) hJ2int
