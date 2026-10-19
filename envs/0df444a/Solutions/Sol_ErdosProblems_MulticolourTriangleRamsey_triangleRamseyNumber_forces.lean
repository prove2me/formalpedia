-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.triangleRamseyNumber_forces
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.631419+00:00
-- url     : https://prove2.me/submissions/c6cee2a8-79b6-45bc-a535-0339c14545ca

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_exists_forcesMonochromaticTriangle

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (k : ℕ) :
    ForcesMonochromaticTriangle (triangleRamseyNumber k) k := by
  exact Nat.sInf_mem (exists_forcesMonochromaticTriangle k)
end ErdosProblems.MulticolourTriangleRamsey
