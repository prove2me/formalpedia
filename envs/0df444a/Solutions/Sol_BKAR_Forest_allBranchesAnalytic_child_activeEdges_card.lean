-- Prove2me | solution 1 for BKAR.Forest.allBranchesAnalytic.child_activeEdges_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:14:58.293905+00:00
-- url     : https://prove2.me/submissions/21ea97f7-14b6-493c-a4bf-7932a45f8a86

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Theorems.Thm_BKAR_Forest_ActiveExtension_activeEdges_card_lt
import Theorems.Thm_BKAR_Forest_EdgeExtension_activeEdges_card_lt
import Theorems.Thm_BKAR_Forest_allBranchesAnalytic_of_le


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
namespace allBranchesAnalytic
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (e : {e // e ∈ F.activeEdges})
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ)
    {t : ℝ} (ht : t ∈ Set.uIcc 0 top) :
    allBranchesAnalytic choices
      (choices F e).forest.activeEdges.card
      (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t]) t ρ := by
  have hcard_pos : 0 < F.activeEdges.card :=
    Finset.card_pos.mpr ⟨e.val, e.property⟩
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcard_pos) with
    ⟨n, hn⟩
  rw [hn] at hanalytic
  rcases hanalytic with ⟨_hbound, _hρ, _hint, _hstd, _hrec, hchild⟩
  have hchild_le :
      (choices F e).forest.activeEdges.card ≤ n := by
    have hlt :
        (choices F e).forest.activeEdges.card < F.activeEdges.card :=
      (choices F e).activeEdges_card_lt
    rw [hn] at hlt
    exact Nat.lt_succ_iff.mp hlt
  exact allBranchesAnalytic_of_le choices hchild_le (hchild e t ht)
end allBranchesAnalytic
end BKAR.Forest
