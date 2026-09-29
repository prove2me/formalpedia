-- Prove2me | solution 1 for FamousTheorems.connected_iff_interval_order_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:59:50.42881+00:00
-- url     : https://prove2.me/submissions/29572f97-5219-4944-9807-2f90fc778d90

import Mathlib

theorem solution {α : Type*} [TopologicalSpace α] [ConditionallyCompleteLinearOrder α] [OrderTopology α] [DenselyOrdered α]
    {s : Set α} : IsPreconnected s ↔ s.OrdConnected :=
  isPreconnected_iff_ordConnected
