-- Prove2me | solution 1 for FamousTheorems.locally_path_connected_connected_path_connected_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:01:13.838004+00:00
-- url     : https://prove2.me/submissions/94fc007b-6381-4025-b960-7b17f9be4541

import Mathlib

theorem solution (X : Type*) [TopologicalSpace X] [LocallyPathConnectedSpace X] : PathConnectedSpace X ↔ ConnectedSpace X :=
  pathConnectedSpace_iff_connectedSpace
