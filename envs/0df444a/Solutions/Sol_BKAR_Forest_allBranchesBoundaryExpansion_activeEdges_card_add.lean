-- Prove2me | solution 1 for BKAR.Forest.allBranchesBoundaryExpansion_activeEdges_card_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:44:44.180134+00:00
-- url     : https://prove2.me/submissions/6ccdb9d6-70f8-437b-82d4-5edb3aae3e1e

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_Forest_allBranchesBoundaryExpansion_stable_of_activeEdges_card_le

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V) :
    ∀ (k : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (ρ : (Edge V → ℝ) → ℝ),
      allBranchesBoundaryExpansion choices (F.activeEdges.card + k)
          F pref prefixTs top ρ =
        allBranchesBoundaryExpansion choices F.activeEdges.card
          F pref prefixTs top ρ
  | 0, F, pref, prefixTs, top, ρ => by
      rw [Nat.add_zero]
  | k + 1, F, pref, prefixTs, top, ρ => by
      rw [Nat.add_succ]
      have hle : F.activeEdges.card ≤ F.activeEdges.card + k :=
        Nat.le_add_right _ _
      rw [allBranchesBoundaryExpansion_stable_of_activeEdges_card_le
        choices (F.activeEdges.card + k) F pref prefixTs top ρ hle]
      exact
        solution choices k
          F pref prefixTs top ρ
end BKAR.Forest
