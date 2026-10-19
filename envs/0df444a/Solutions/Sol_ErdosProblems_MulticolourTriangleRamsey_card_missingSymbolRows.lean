-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.card_missingSymbolRows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/07e0e0d0-b027-432b-8494-61decdcd7c17

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (H m : ℕ)
    (T : Finset (Fin m → Fin H)) (symbol : Fin H) :
    (missingSymbolRows H m T symbol).card =
      (H - 1) ^ T.card * H ^ (H ^ m - T.card) := by
  classical
  calc
    (missingSymbolRows H m T symbol).card =
        ∏ column : Fin m → Fin H,
          if column ∈ T then H - 1 else H := by
      rw [missingSymbolRows, Fintype.card_piFinset]
      apply Finset.prod_congr rfl
      intro column _
      split_ifs <;> simp
    _ = (H - 1) ^ T.card * H ^ (H ^ m - T.card) := by
      rw [Finset.prod_ite]
      simp [Finset.filter_notMem_eq_sdiff, Finset.card_sdiff_of_subset]
end ErdosProblems.MulticolourTriangleRamsey
