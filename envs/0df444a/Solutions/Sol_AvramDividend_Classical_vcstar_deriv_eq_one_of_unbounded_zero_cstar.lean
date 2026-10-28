-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_deriv_eq_one_of_unbounded_zero_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:01:28.49163+00:00
-- url     : https://prove2.me/submissions/c02513da-b143-4855-a189-94010a86f1c7

import Theorems.Thm_AvramDividend_Classical_vcstar_eq_positive_part_of_unbounded_zero_cstar
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- A zero optimal barrier makes the verification candidate locally
the identity at every strictly positive reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hc0 : cstar W = 0) :
    ∀ x : ℝ, 0 < x →
      DifferentiableAt ℝ (vcstar W) x ∧ deriv (vcstar W) x = 1 := by
  intro x hx
  have heq : vcstar W =ᶠ[nhds x] (fun y : ℝ => y) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    rw [vcstar_eq_positive_part_of_unbounded_zero_cstar
      X q hq W hW hnbv hc0 y]
    exact max_eq_left (le_of_lt hy)
  have hd : HasDerivAt (vcstar W) 1 x :=
    (hasDerivAt_id x).congr_of_eventuallyEq heq
  exact ⟨hd.differentiableAt, hd.deriv⟩
