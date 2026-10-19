-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.exists_forcesMonochromaticTriangle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.631419+00:00
-- url     : https://prove2.me/submissions/31c849d4-c8d2-4936-908e-38d1dab68d09

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_forcesMonochromaticTriangle_zero
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_forcesMonochromaticTriangle_succ

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (k : ℕ) :
    ∃ n : ℕ, ForcesMonochromaticTriangle n k := by
  induction k with
  | zero =>
      exact ⟨2, forcesMonochromaticTriangle_zero⟩
  | succ k ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨1 + (k + 1) * n, forcesMonochromaticTriangle_succ hn⟩
end ErdosProblems.MulticolourTriangleRamsey
