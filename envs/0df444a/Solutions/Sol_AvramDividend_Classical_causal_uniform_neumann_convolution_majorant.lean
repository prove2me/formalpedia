-- Prove2me | solution 1 for AvramDividend.Classical.causal_uniform_neumann_convolution_majorant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T21:06:26.907698+00:00
-- url     : https://prove2.me/submissions/7ba6c441-df47-4e10-ab76-bdee629fa759

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter

/-- Uniformly bounded Neumann partial sums admit an integrable causal convolution majorant. -/
theorem solution
    (B : ℝ → ℝ) (Q : ℕ → ℝ → ℝ)
    (hB : ∀ x : ℝ, IntegrableOn (fun s : ℝ => B (x - s))
      (Ioc (0 : ℝ) x) volume)
    (hQ : ∀ x : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, ∀ s : ℝ,
        ‖(∑ i ∈ Finset.range (n + 1), Q i) s‖ ≤ C) :
    ∀ x : ℝ, ∃ D : ℝ → ℝ,
      IntegrableOn D (Ioc (0 : ℝ) x) volume ∧
      (∀ n : ℕ, ∀ᵐ s ∂(volume.restrict (Ioc (0 : ℝ) x)),
        ‖B (x - s) * (∑ i ∈ Finset.range (n + 1), Q i) s‖ ≤ D s) := by
  intro x
  obtain ⟨C, hC, hbound⟩ := hQ x
  refine ⟨(fun s : ℝ => C * ‖B (x - s)‖), ?_, ?_⟩
  · exact (hB x).norm.const_mul C
  · intro n
    apply Filter.Eventually.of_forall
    intro s
    calc
      ‖B (x - s) * (∑ i ∈ Finset.range (n + 1), Q i) s‖ =
          ‖B (x - s)‖ * ‖(∑ i ∈ Finset.range (n + 1), Q i) s‖ := norm_mul _ _
      _ ≤ ‖B (x - s)‖ * C :=
        mul_le_mul_of_nonneg_left (hbound n s) (norm_nonneg _)
      _ = C * ‖B (x - s)‖ := mul_comm _ _
