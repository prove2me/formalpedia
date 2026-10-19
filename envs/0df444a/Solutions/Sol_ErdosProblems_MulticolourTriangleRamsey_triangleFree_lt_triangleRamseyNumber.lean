-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.triangleFree_lt_triangleRamseyNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/294c08bf-a061-473b-868b-a40bcafbd5f1

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_forcesMonochromaticTriangle_mono
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_triangleRamseyNumber_forces

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution {n k : ℕ}
    (C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k))
    (hC : TriangleFree C) :
    n < triangleRamseyNumber k := by
  by_contra hnot
  have hle : triangleRamseyNumber k ≤ n := by omega
  have hforcing : ForcesMonochromaticTriangle n k :=
    forcesMonochromaticTriangle_mono hle
      (triangleRamseyNumber_forces k)
  exact hforcing C hC
end ErdosProblems.MulticolourTriangleRamsey
