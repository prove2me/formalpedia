-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_two_scale_budget_forces_B_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T11:21:03.159939+00:00
-- url     : https://prove2.me/submissions/eac2e465-10cd-47e8-a7c0-d723a4986ab1

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Filter
open scoped Topology
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (a : ℝ) (F B M E₁ E₂ : Ω → ℝ)
    (hF : ∀ᵐ ω ∂P, 0 ≤ F ω)
    (hB : ∀ᵐ ω ∂P, B ω ≤ 0)
    (hBmeas : AEStronglyMeasurable B P)
    (hM : Integrable M P)
    (hE₁ : Integrable (fun ω => max (E₁ ω) 0) P)
    (hE₂ : Integrable (fun ω => max (E₂ ω) 0) P)
    (hBudget : ∀ᵐ ω ∂P,
      F ω ≤ a + M ω + B ω +
        max (E₁ ω) 0 + max (E₂ ω) 0) :
    Integrable B P := by
  have hEnv : Integrable
      (fun ω => |a| + ‖M ω‖ +
        max (E₁ ω) 0 + max (E₂ ω) 0) P := by
    exact (((integrable_const (|a| : ℝ)).add hM.norm).add hE₁).add hE₂
  apply Integrable.mono' hEnv hBmeas
  filter_upwards [hF, hB, hBudget] with ω hFω hBω hBudgetω
  rw [Real.norm_eq_abs, abs_of_nonpos hBω, Real.norm_eq_abs]
  have ha : a ≤ |a| := le_abs_self a
  have hm : M ω ≤ |M ω| := le_abs_self (M ω)
  linarith
