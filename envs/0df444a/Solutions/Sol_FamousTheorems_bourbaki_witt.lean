-- Prove2me | solution 1 for FamousTheorems.bourbaki_witt
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:23:22.006343+00:00
-- url     : https://prove2.me/submissions/e4fb4b3d-8fbf-484f-8480-271ef12e7586

import Mathlib

theorem solution {α : Type*} [ChainCompletePartialOrder α] {f : α → α} [Nonempty α] (le_map : ∀ x, x ≤ f x) :
    (Function.fixedPoints f).Nonempty :=
  ChainCompletePartialOrder.nonempty_fixedPoints_of_inflationary le_map
