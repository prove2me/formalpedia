-- Prove2me | solution 1 for BKAR.Forest.allBranchesAnalytic.child_recursive_sum_intervalIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:15:37.053177+00:00
-- url     : https://prove2.me/submissions/5c8dd28a-726a-4592-a301-298f568b5e3e

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping

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
        F pref prefixTs top ρ) :
    IntervalIntegrable
      (fun t : ℝ =>
        Finset.sum (choices F e).forest.activeEdges.attach
          (fun e' => ∫ s in 0..t,
            allBranchesBoundaryExpansion choices
              (choices (choices F e).forest e').forest.activeEdges.card
              (choices (choices F e).forest e').forest
              ((pref ++ [e.val]) ++ [e'.val])
              ((prefixTs ++ [t]) ++ [s]) s ρ))
      MeasureTheory.volume 0 top := by
  have hcard_pos : 0 < F.activeEdges.card :=
    Finset.card_pos.mpr ⟨e.val, e.property⟩
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcard_pos) with
    ⟨n, hn⟩
  rw [hn] at hanalytic
  rcases hanalytic with ⟨_hbound, _hρ, _hint, _hstd, hrec, _hchild⟩
  exact hrec e
end allBranchesAnalytic
end BKAR.Forest
