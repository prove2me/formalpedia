-- Prove2me | solution 1 for AvramDividend.Classical.chat03_actual_grid_terminal_tie_clock_eq_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T21:17:57.078925+00:00
-- url     : https://prove2.me/submissions/e2b46d0f-35b2-4d68-99cb-00099656e7a1

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_hittingBtwn_terminal_payoff_of_no_early_hit
import Mathlib.Probability.Process.HittingTime
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-!
If the strict continuous two-sided passage infimum equals T, then
the genuine bounded hittingBtwn sampled clock, clipped at T, is
exactly T for every grid whose final physical time covers T.
Crossings after T are allowed, so no atom-free assumption is needed.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (T mesh : ℝ≥0) (m : ℕ)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} T)
    (hcap : T ≤ (m : ℝ≥0) * mesh) :
    min (((hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * mesh) ξ))
      (Set.Ioi (0 : ℝ)) 0 m ω : ℕ) : ℝ≥0) * mesh) T = T := by
  apply chat03_hittingBtwn_terminal_payoff_of_no_early_hit
    (fun (j : ℕ) ξ => max
      (X.X ((j : ℝ≥0) * mesh) ξ - upper)
      (lower - X.X ((j : ℝ≥0) * mesh) ξ))
    (Set.Ioi (0 : ℝ)) ω mesh T m hcap
  intro j hj hmem
  have hcase :
      X.X ((j : ℝ≥0) * mesh) ω < lower ∨
      upper < X.X ((j : ℝ≥0) * mesh) ω := by
    have hmax : upper < X.X ((j : ℝ≥0) * mesh) ω ∨
        X.X ((j : ℝ≥0) * mesh) ω < lower := by
      simpa only [Set.mem_Ioi, lt_max_iff, sub_pos] using hmem
    exact hmax.symm
  exact (not_lt_of_ge (hτ.1 hcase)) hj
