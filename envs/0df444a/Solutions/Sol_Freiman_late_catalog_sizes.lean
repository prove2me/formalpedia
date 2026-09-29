-- Prove2me | solution 1 for Freiman.late_catalog_sizes
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:21:45.414792+00:00
-- url     : https://prove2.me/submissions/b81b8d00-59e7-46a4-bc53-3e351edb9fbc

import Definitions.Def_Freiman_lateModel
import Definitions.Def_Freiman_lateData
open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem solution : lateCatalog.bounds.size = 341 ∧ lateCatalog.witnesses.size = 1473 ∧ lateCatalog.endpoints.size = 162 ∧ lateCatalog.paths.size = 63 ∧ lateCatalog.proofs.size = 1494 ∧ lateCatalog.rectangles.size = 32 := by
  simp only [lateCatalog, Array.size_append]
  decide +kernel

#print axioms solution
