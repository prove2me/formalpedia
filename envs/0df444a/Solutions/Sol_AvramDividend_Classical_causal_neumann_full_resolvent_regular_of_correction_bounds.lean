-- Prove2me | solution 1 for AvramDividend.Classical.causal_neumann_full_resolvent_regular_of_correction_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:04:17.909982+00:00
-- url     : https://prove2.me/submissions/c1edf3ec-f779-41b9-ae7d-a1af788f34f1

import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_causal_neumann_geometric_series_continuousOn_nonnegative
import Theorems.Thm_AvramDividend_Classical_causal_neumann_geometric_correction_contDiffOn_one

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set

/-- Geometrically controlled signed Neumann corrections yield a continuous
full resolvent, differentiable for every strictly positive time. -/
theorem solution
    (P H : ℕ → ℝ → ℝ) (a ρ w : ℝ)
    (ha : 0 < a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hw : 0 ≤ w)
    (hP : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      |P n x| ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x)
    (hH : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      |H n x| ≤ ρ ^ (n + 1) / a)
    (hHcont : ∀ n : ℕ, ContinuousOn (H n) (Ici (0 : ℝ)))
    (hHasDeriv : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      HasDerivAt (H n) (P n x / a - w * H n x) x)
    (hCont : ∀ ε R : ℝ, 0 < ε → ∀ n : ℕ,
      ContinuousOn (fun x : ℝ => P n x / a - w * H n x) (Ioo ε R)) :
    ∃ g : ℝ → ℝ,
      (g = fun y : ℝ => 1 / a +
        Real.exp (w * y) * (∑' n : ℕ, H n y)) ∧
      ContinuousOn g (Ici (0 : ℝ)) ∧
      ContDiffOn ℝ 1 g (Ioi (0 : ℝ)) := by
  have hseries := causal_neumann_geometric_series_continuousOn_nonnegative
    H a ρ ha hρ0 hρ1 hHcont hH
  have hC1 := causal_neumann_geometric_correction_contDiffOn_one
    P H a ρ w ha hρ0 hρ1 hw hP hH hHasDeriv hCont
  have hexp0 : ContinuousOn (fun y : ℝ => Real.exp (w * y))
      (Ici (0 : ℝ)) := by fun_prop
  have hexp1 : ContDiffOn ℝ 1 (fun y : ℝ => Real.exp (w * y))
      (Ioi (0 : ℝ)) := by fun_prop
  refine ⟨(fun y : ℝ => 1 / a +
      Real.exp (w * y) * (∑' n : ℕ, H n y)), rfl, ?_, ?_⟩
  · exact continuousOn_const.add (hexp0.mul hseries.1)
  · exact contDiffOn_const.add (hexp1.mul hC1)
