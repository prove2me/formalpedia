-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_capHJB52_original_C1_positive_deriv_bound_to_closed_cap_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T17:26:27.474057+00:00
-- url     : https://prove2.me/submissions/6691753b-7364-471a-be19-470a30f42295

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal Topology
noncomputable section

theorem solution
    (w : ℝ → ℝ) (a c : ℝ) (ha : a < c) (K : ℝ≥0)
    (hwCont : ContinuousOn w (Icc a c))
    (hDiff : ∀ y ∈ Ioo a c, DifferentiableAt ℝ w y)
    (hDeriv : ∀ y ∈ Ioo a c, ‖deriv w y‖₊ ≤ K) :
    LipschitzOnWith K w (Icc a c) := by
  have hOpen : LipschitzOnWith K w (Ioo a c) :=
    (convex_Ioo a c).lipschitzOnWith_of_nnnorm_deriv_le hDiff hDeriv
  have hclosure : closure (Ioo a c) = Icc a c :=
    closure_Ioo (ne_of_lt ha)
  have hContClosure : ContinuousOn w (closure (Ioo a c)) := by
    simpa only [hclosure] using hwCont
  have hClosed := hOpen.closure hContClosure
  simpa only [hclosure] using hClosed
