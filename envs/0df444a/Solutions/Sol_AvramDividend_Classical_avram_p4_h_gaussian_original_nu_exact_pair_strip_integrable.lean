-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_h_gaussian_original_nu_exact_pair_strip_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:50:19.938193+00:00
-- url     : https://prove2.me/submissions/9c2cd66a-8102-4f0e-9719-071013432682

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_nu_quadratic_real_energy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every exact cutoff-pair band of the original Lévy measure has finite
real quadratic energy, including an atom at the upper cutoff. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n m : ℕ) :
    IntegrableOn (fun z : ℝ => z ^ 2)
      (Ioc (-(1 / (((min n m : ℕ) : ℝ) + 1)))
           (-(1 / (((max n m : ℕ) : ℝ) + 1)))) X.ν := by
  let C : Set ℝ := Ioc (-(1 / (((min n m : ℕ) : ℝ) + 1)))
                         (-(1 / (((max n m : ℕ) : ℝ) + 1)))
  let D : Set ℝ := Ioc (-(1 / (((min n m : ℕ) : ℝ) + 1))) 0
  have hSub : C ⊆ D := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    have hd : 0 ≤ (1 : ℝ) / (((max n m : ℕ) : ℝ) + 1) := by
      positivity
    linarith [hz.2]
  have hTail :=
    (avram_p4_h_gaussian_original_nu_quadratic_real_energy X (min n m)).1
  change IntegrableOn (fun z : ℝ => z ^ 2) C X.ν
  exact hTail.mono_set hSub
