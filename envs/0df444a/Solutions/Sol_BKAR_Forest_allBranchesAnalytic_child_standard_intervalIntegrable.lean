-- Prove2me | solution 1 for BKAR.Forest.allBranchesAnalytic.child_standard_intervalIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:15:31.293796+00:00
-- url     : https://prove2.me/submissions/160b555e-d5ed-4744-94f2-3c7506dca356

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse


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
      (fun t : ℝ => mixedPartialList (pref ++ [e.val]).reverse ρ
        ((choices F e).forest.standardInterp
          ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
            (prefixTs ++ [t]))))
      MeasureTheory.volume 0 top := by
  have hcard_pos : 0 < F.activeEdges.card :=
    Finset.card_pos.mpr ⟨e.val, e.property⟩
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcard_pos) with
    ⟨n, hn⟩
  rw [hn] at hanalytic
  rcases hanalytic with ⟨_hbound, _hρ, _hint, hstd, _hrec, _hchild⟩
  exact hstd e
end allBranchesAnalytic
end BKAR.Forest
