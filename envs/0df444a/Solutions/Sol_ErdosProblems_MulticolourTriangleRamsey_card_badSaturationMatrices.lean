-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.card_badSaturationMatrices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/5756bd5b-36d2-49d5-8d51-3da3b514e63c

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (H m s : ℕ)
    (T : Finset (Fin m → Fin H)) :
    (badSaturationMatrices H m s T).card =
      (badSaturationRows H m T).card ^ s := by
  classical
  simp [badSaturationMatrices, Fintype.card_piFinset]
end ErdosProblems.MulticolourTriangleRamsey
