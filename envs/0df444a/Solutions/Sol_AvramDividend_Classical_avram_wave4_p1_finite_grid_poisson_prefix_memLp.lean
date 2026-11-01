-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_finite_grid_poisson_prefix_memLp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:27:58.061067+00:00
-- url     : https://prove2.me/submissions/458bccf8-ad06-4d97-a70a-188c9071b62e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_past_weighted_poisson_count_l2_isometry

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Nat BigOperators

/-- All finite sums of genuine past-weighted compensated Poisson count cells
are square-integrable. No joint independence across distinct cells is needed
for this integrability, only weight-vs-own-count independence per cell. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (H : ℕ → Ω → ℝ) (K : ℕ → Ω → ℕ) (r : ℕ → ℝ≥0)
    (hHm : ∀ i, Measurable (H i))
    (hHSq : ∀ i, Integrable (fun ω => (H i ω) ^ 2) P)
    (hKm : ∀ i, Measurable (K i))
    (hKlaw : ∀ i, HasLaw (K i) (poissonMeasure (r i)) P)
    (hIndep : ∀ i, IndepFun (H i) (K i) P) :
    ∀ n, MemLp (fun ω =>
      ∑ i ∈ Finset.range n, H i ω * ((K i ω : ℝ) - (r i : ℝ))) 2 P := by
  classical
  have hCell : ∀ i, MemLp
      (fun ω => H i ω * ((K i ω : ℝ) - (r i : ℝ))) 2 P := by
    intro i
    have hHi : Measurable (H i) := hHm i
    have hKi : Measurable (K i) := hKm i
    have hIncMeas :
        Measurable (fun ω => H i ω * ((K i ω : ℝ) - (r i : ℝ))) := by
      fun_prop
    have hW :=
      AvramDividend.Classical.avram_wave4_p1_past_weighted_poisson_count_l2_isometry
        P (H i) (hHm i) (hHSq i) (K i) (hKm i) (r i) (hKlaw i) (hIndep i)
    exact (memLp_two_iff_integrable_sq hIncMeas.aestronglyMeasurable).2 hW.1
  intro n
  induction n with
  | zero =>
      have hZeroMeas : AEStronglyMeasurable (fun _ : Ω => (0 : ℝ)) P :=
        aestronglyMeasurable_const
      have hZero : MemLp (fun _ : Ω => (0 : ℝ)) 2 P :=
        (memLp_two_iff_integrable_sq hZeroMeas).2 (by
          simpa using (integrable_const (0 : ℝ) :
            Integrable (fun _ : Ω => (0 : ℝ)) P))
      simpa using hZero
  | succ n ih =>
      have hPoint :
          (fun ω => ∑ i ∈ Finset.range (n + 1),
            H i ω * ((K i ω : ℝ) - (r i : ℝ))) =
          (fun ω => ∑ i ∈ Finset.range n,
            H i ω * ((K i ω : ℝ) - (r i : ℝ))) +
          (fun ω => H n ω * ((K n ω : ℝ) - (r n : ℝ))) := by
        funext ω
        simp only [Finset.sum_range_succ, Pi.add_apply]
      rw [hPoint]
      exact ih.add (hCell n)
