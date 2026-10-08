-- Prove2me | solution 1 for AvramDividend.Classical.continuous_measureReal_Iic_of_finite_noAtoms
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T13:33:48.413487+00:00
-- url     : https://prove2.me/submissions/5de6a408-0fa3-4142-80d2-277dc7c9379a

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

theorem solution
    (μ : Measure ℝ) [NullSingletonClass μ]
    (hfin : ∀ x : ℝ, μ (Iic x) ≠ ⊤) :
    Continuous (fun x : ℝ => μ.real (Iic x)) := by
  rw [continuous_iff_continuousAt]
  intro x
  let a : ℝ := x + 1
  have hxa : x < a := by
    dsimp [a]
    linarith
  have hμlt : μ (Iic a) < ⊤ :=
    lt_top_iff_ne_top.mpr (hfin a)
  have hint :
      IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Iic a) μ := by
    exact (integrableOn_const_iff).2 (Or.inr hμlt)
  have hc :
      ContinuousOn
        (fun b : ℝ => ∫ _ in Iic b, (1 : ℝ) ∂μ) (Iic a) :=
    hint.continuousOn_Iic_primitive_Iic
  have hca :
      ContinuousAt
        (fun b : ℝ => ∫ _ in Iic b, (1 : ℝ) ∂μ) x :=
    hc.continuousAt (Iic_mem_nhds hxa)
  simpa only [setIntegral_one_eq_measureReal] using hca
