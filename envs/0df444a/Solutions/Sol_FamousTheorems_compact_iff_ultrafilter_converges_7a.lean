-- Prove2me | solution 1 for FamousTheorems.compact_iff_ultrafilter_converges_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:59:54.855754+00:00
-- url     : https://prove2.me/submissions/41ac8fe3-86b5-4449-a2d5-92d71393d12b

import Mathlib

theorem solution {X : Type*} [TopologicalSpace X] {s : Set X} :
    IsCompact s ↔ ∀ f : Ultrafilter X, (f : Filter X) ≤ Filter.principal s → ∃ x ∈ s, (f : Filter X) ≤ nhds x :=
  isCompact_iff_ultrafilter_le_nhds
