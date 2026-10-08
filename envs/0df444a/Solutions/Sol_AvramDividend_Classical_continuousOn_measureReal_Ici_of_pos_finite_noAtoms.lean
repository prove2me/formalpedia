-- Prove2me | solution 1 for AvramDividend.Classical.continuousOn_measureReal_Ici_of_pos_finite_noAtoms
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T15:12:58.622769+00:00
-- url     : https://prove2.me/submissions/744e9610-6e63-4a3d-b31f-915bb4586e78

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

theorem solution
    (μ : Measure ℝ) [NullSingletonClass μ]
    (hfin : ∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) :
    ContinuousOn (fun x : ℝ => μ.real (Ici x)) (Ioi 0) := by
  intro x hx
  have hxpos : 0 < x := by
    simpa only [Set.mem_Ioi] using hx
  let a : ℝ := x / 2
  have ha : 0 < a := by
    dsimp [a]
    linarith
  have hax : a < x := by
    dsimp [a]
    linarith
  have hμlt : μ (Ici a) < ⊤ :=
    lt_top_iff_ne_top.mpr (hfin a ha)
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
  simpa only [setIntegral_one_eq_measureReal] using hca.continuousWithinAt
