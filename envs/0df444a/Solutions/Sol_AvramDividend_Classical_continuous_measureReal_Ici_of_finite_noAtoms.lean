-- Prove2me | solution 1 for AvramDividend.Classical.continuous_measureReal_Ici_of_finite_noAtoms
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T13:34:03.545004+00:00
-- url     : https://prove2.me/submissions/0c9f3212-5ec1-4d40-a65a-89d9df79c155

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

theorem solution
    (μ : Measure ℝ) [NullSingletonClass μ]
    (hfin : ∀ x : ℝ, μ (Ici x) ≠ ⊤) :
    Continuous (fun x : ℝ => μ.real (Ici x)) := by
  rw [continuous_iff_continuousAt]
  intro x
  let a : ℝ := x - 1
  have hax : a < x := by
    dsimp [a]
    linarith
  have hμlt : μ (Ici a) < ⊤ :=
    lt_top_iff_ne_top.mpr (hfin a)
  have hint :
      IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ici a) μ := by
    exact (integrableOn_const_iff).2 (Or.inr hμlt)
  have hc :
      ContinuousOn
        (fun b : ℝ => ∫ _ in Ici b, (1 : ℝ) ∂μ) (Ici a) :=
    hint.continuousOn_Ici_primitive_Ici
  have hca :
      ContinuousAt
        (fun b : ℝ => ∫ _ in Ici b, (1 : ℝ) ∂μ) x :=
    hc.continuousAt (Ici_mem_nhds hax)
  simpa only [setIntegral_one_eq_measureReal] using hca
