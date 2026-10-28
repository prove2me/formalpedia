-- Prove2me | solution 1 for AvramDividend.Classical.causal_neumann_measurable_from_c1_primitives
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T22:27:18.774191+00:00
-- url     : https://prove2.me/submissions/90e30c7b-e343-448c-a0f9-84dfd6a11714

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Exponentially weighted continuous primitives are measurable on causal intervals. -/
theorem solution
    (H Q : ℕ → ℝ → ℝ) (a w : ℝ)
    (hQ0 : Q 0 = fun _ : ℝ => 1 / a)
    (hQstep : ∀ n : ℕ, Q (n + 1) =
      fun x : ℝ => Real.exp (w * x) * H n x)
    (hHcont : ∀ n : ℕ, ContinuousOn (H n) (Ici (0 : ℝ))) :
    ∀ x : ℝ, ∀ i : ℕ, AEStronglyMeasurable
      (Q i) (volume.restrict (Ioc (0 : ℝ) x)) := by
  have hexp : ContinuousOn
      (fun x : ℝ => Real.exp (w * x)) (Ici (0 : ℝ)) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  have hQcont : ∀ i : ℕ, ContinuousOn (Q i) (Ici (0 : ℝ)) := by
    intro i
    cases i with
    | zero =>
        rw [hQ0]
        exact continuousOn_const
    | succ n =>
        rw [hQstep n]
        exact hexp.mul (hHcont n)
  intro x i
  have hsubset : Ioc (0 : ℝ) x ⊆ Ici (0 : ℝ) := by
    intro s hs
    exact le_of_lt hs.1
  exact ((hQcont i).mono hsubset).aestronglyMeasurable measurableSet_Ioc
