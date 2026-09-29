-- Prove2me | solution 1 for FamousTheorems.heine_borel
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T01:51:16.361787+00:00
-- url     : https://prove2.me/submissions/c662e86b-6679-49d9-a120-1cdcb1abff7b

import Mathlib

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

theorem solution {α : Type*} {s : Set α} [MetricSpace α] [ProperSpace α] :
    IsCompact s ↔ IsClosed s ∧ Bornology.IsBounded s :=
  Metric.isCompact_iff_isClosed_bounded
