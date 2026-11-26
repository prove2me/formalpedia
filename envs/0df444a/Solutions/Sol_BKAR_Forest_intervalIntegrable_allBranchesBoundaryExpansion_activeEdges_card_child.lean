-- Prove2me | solution 1 for BKAR.Forest.intervalIntegrable_allBranchesBoundaryExpansion_activeEdges_card_child
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:31:55.771797+00:00
-- url     : https://prove2.me/submissions/d74da824-f15f-489b-b77b-330a8ec41d50

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_Forest_mixedPartialList_cons_interpWithFill_eq_allBranchesBoundaryExpansion_child

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (e : {e // e ∈ F.activeEdges})
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ) :
    IntervalIntegrable
      (fun t : ℝ =>
        allBranchesBoundaryExpansion choices
          (choices F e).forest.activeEdges.card
          (choices F e).forest (pref ++ [e.val])
          (prefixTs ++ [t]) t ρ)
      MeasureTheory.volume 0 top := by
  have hanalyticExact := hanalytic
  have hcard_pos : 0 < F.activeEdges.card :=
    Finset.card_pos.mpr ⟨e.val, e.property⟩
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcard_pos) with
    ⟨n, hn⟩
  rw [hn] at hanalytic
  rcases hanalytic with ⟨_hbound, _hρ, hint, _hstd, _hrec, _hchild⟩
  refine (hint e.val e.property).congr ?_
  intro t ht
  have ht_uIcc : t ∈ Set.uIcc 0 top :=
    Set.uIoc_subset_uIcc ht
  exact
    mixedPartialList_cons_interpWithFill_eq_allBranchesBoundaryExpansion_child
      choices F e pref prefixTs hpref hprefixTs top ρ hanalyticExact
      ht_uIcc
end BKAR.Forest
