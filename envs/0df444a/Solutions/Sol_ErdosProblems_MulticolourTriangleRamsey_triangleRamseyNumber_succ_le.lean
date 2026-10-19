-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.triangleRamseyNumber_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.631419+00:00
-- url     : https://prove2.me/submissions/0980bf2c-227f-4e35-9c66-24f18c18bcae

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_forcesMonochromaticTriangle_succ
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_triangleRamseyNumber_forces

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (k : ℕ) :
    triangleRamseyNumber (k + 1) ≤
      1 + (k + 1) * triangleRamseyNumber k := by
  apply Nat.sInf_le
  exact forcesMonochromaticTriangle_succ (triangleRamseyNumber_forces k)
end ErdosProblems.MulticolourTriangleRamsey
