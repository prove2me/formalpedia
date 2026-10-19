-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.triangleRamseyNumber_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/39c3ac1f-c691-4892-9e02-c28484cd7ac7

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_cliqueFree_compRight_embedding
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_triangleRamseyNumber_forces

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution {k l : ℕ} (hkl : k ≤ l) :
    triangleRamseyNumber k ≤ triangleRamseyNumber l := by
  apply Nat.sInf_le
  intro C hC
  have hlarge :
      TriangleFree (C.compRight (Fin.castLEEmb hkl)) :=
    cliqueFree_compRight_embedding C (Fin.castLEEmb hkl) hC
  exact triangleRamseyNumber_forces l
    (C.compRight (Fin.castLEEmb hkl)) hlarge
end ErdosProblems.MulticolourTriangleRamsey
