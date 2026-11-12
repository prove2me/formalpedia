-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_cp_residual_future_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T09:33:29.610128+00:00
-- url     : https://prove2.me/submissions/527ae5ad-47fd-4531-a89f-59566d6e7586

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
import Theorems.Thm_AvramDividend_Classical_avram_a06_compound_jumpCount_measurable_public
import Theorems.Thm_AvramDividend_Classical_avram_a06_random_index_coordinate_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

/-- Measurability of the original same-space residual waiting time and
    its entire random-count future suffix. -/
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (s : ℝ≥0) :
    Measurable (fun ω => (τ (LevyFoundations.jumpCount
        (fun i => LevyFoundations.arrival τ i ω) (s : ℝ)) ω -
      ((s : ℝ) - ∑ i ∈ Finset.range
        (LevyFoundations.jumpCount
          (fun i => LevyFoundations.arrival τ i ω) (s : ℝ)), τ i ω),
      fun j : ℕ => τ (LevyFoundations.jumpCount
        (fun i => LevyFoundations.arrival τ i ω) (s : ℝ) + 1 + j) ω)) := by
  let K : ((ℕ → ℝ) × (ℕ → ℝ)) → ℕ := fun ω =>
    LevyFoundations.jumpCount (fun i => LevyFoundations.arrival τ i ω) (s : ℝ)
  have hτ (n : ℕ) : Measurable (τ n) := hd.measurable_interarrival n
  have hK : Measurable K := by
    exact AvramDividend.Classical.avram_a06_compound_jumpCount_measurable_public τ hτ (s : ℝ)
  have hAt : Measurable (fun ω => τ (K ω) ω) :=
    AvramDividend.Classical.avram_a06_random_index_coordinate_measurable
      τ hτ K hK
  have hPrefixOne (n : ℕ) :
      Measurable (fun ω => ∑ i ∈ Finset.range n, τ i ω) := by
    exact Finset.measurable_sum _ (fun i _ => hτ i)
  have hPrefix :
      Measurable (fun ω => ∑ i ∈ Finset.range (K ω), τ i ω) :=
    AvramDividend.Classical.avram_a06_random_index_coordinate_measurable
      (fun n ω => ∑ i ∈ Finset.range n, τ i ω) hPrefixOne K hK
  have hFuture : Measurable (fun ω (j : ℕ) => τ (K ω + 1 + j) ω) := by
    rw [measurable_pi_iff]
    intro j
    have hj : Measurable (fun ω => K ω + 1 + j) :=
      (hK.add measurable_const).add measurable_const
    exact AvramDividend.Classical.avram_a06_random_index_coordinate_measurable
      τ hτ (fun ω => K ω + 1 + j) hj
  change Measurable (fun ω =>
    (τ (K ω) ω - ((s : ℝ) - ∑ i ∈ Finset.range (K ω), τ i ω),
      fun j : ℕ => τ (K ω + 1 + j) ω))
  exact (hAt.sub (measurable_const.sub hPrefix)).prodMk hFuture
