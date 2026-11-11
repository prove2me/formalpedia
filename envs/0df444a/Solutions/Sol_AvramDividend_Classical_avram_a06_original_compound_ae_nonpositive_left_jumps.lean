-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_compound_ae_nonpositive_left_jumps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T23:26:53.423314+00:00
-- url     : https://prove2.me/submissions/b076775e-2f97-41f1-ae0f-89a2f3696185

import Mathlib.Probability.ConditionalProbability
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_isCadlag
import Theorems.Thm_levy_foundations_compoundDriverArrivalStrictMono
import Theorems.Thm_levy_foundations_compoundDriverArrivalDiverges
import Theorems.Thm_AvramDividend_Classical_avram_a06_compound_driver_all_marks_negative
import Theorems.Thm_AvramDividend_Classical_avram_a06_piecewise_affine_no_positive_left_jumps

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal Topology
noncomputable section

/-- Pass the deterministic nonpositive-jump theorem to original driver
sample paths on a single full-probability event. -/
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∀ᵐ ω ∂P, ∀ (t : ℝ≥0) (l : ℝ), 0 < t →
      Tendsto (fun s : ℝ≥0 =>
        LevyFoundations.compoundPoisson (1 : ℝ) τ Y (s : ℝ) ω)
        (nhdsWithin t (Iio t)) (nhds l) →
      LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ) ω ≤ l := by
  filter_upwards
    [levy_foundations_compoundDriverArrivalStrictMono hd (by norm_num),
      levy_foundations_compoundDriverArrivalDiverges hd (by norm_num),
      avram_a06_compound_driver_all_marks_negative hd]
    with ω hmono htop hmarks
  have hneg : ∀ n, Y n ω ≤ 0 :=
    fun n => (hmarks n).le
  have hpath :=
    avram_a06_piecewise_affine_no_positive_left_jumps
      (0 : ℝ) (1 : ℝ)
      (fun n => LevyFoundations.arrival τ n ω)
      (fun n => Y n ω) hmono htop hneg
  intro t l ht hl
  exact hpath t l ht hl
