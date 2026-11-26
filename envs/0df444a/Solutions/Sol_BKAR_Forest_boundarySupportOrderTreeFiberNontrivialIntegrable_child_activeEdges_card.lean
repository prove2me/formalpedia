-- Prove2me | solution 1 for BKAR.Forest.boundarySupportOrderTreeFiberNontrivialIntegrable.child_activeEdges_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:33:37.591804+00:00
-- url     : https://prove2.me/submissions/9556b78a-18b5-4705-8f4f-df1bdcee9ba7

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiberNontrivialIntegrable_of_le
import Theorems.Thm_BKAR_Forest_ActiveExtension_activeEdges_card_lt
import Theorems.Thm_BKAR_Forest_EdgeExtension_activeEdges_card_lt


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
namespace boundarySupportOrderTreeFiberNontrivialIntegrable
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (e : {e // e ∈ F.activeEdges})
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hfiber :
      boundarySupportOrderTreeFiberNontrivialIntegrable choices
        F.activeEdges.card F pref prefixTs top ρ)
    {t : ℝ} (ht : t ∈ Set.uIcc 0 top) :
    boundarySupportOrderTreeFiberNontrivialIntegrable choices
      (choices F e).forest.activeEdges.card
      (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t]) t ρ := by
  have hcard_pos : 0 < F.activeEdges.card :=
    Finset.card_pos.mpr ⟨e.val, e.property⟩
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcard_pos) with
    ⟨n, hn⟩
  rw [hn] at hfiber
  rcases hfiber with ⟨_hInt, hchild⟩
  have hchild_le :
      (choices F e).forest.activeEdges.card ≤ n := by
    have hlt :
        (choices F e).forest.activeEdges.card < F.activeEdges.card :=
      (choices F e).activeEdges_card_lt
    rw [hn] at hlt
    exact Nat.lt_succ_iff.mp hlt
  exact
    boundarySupportOrderTreeFiberNontrivialIntegrable_of_le choices
      hchild_le (hchild e t ht)
end boundarySupportOrderTreeFiberNontrivialIntegrable
end BKAR.Forest
