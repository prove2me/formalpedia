-- Prove2me | solution 1 for BKAR.Forest.allBranchesAnalytic_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:13:36.572211+00:00
-- url     : https://prove2.me/submissions/45cfc9ff-6f99-4b5d-95e6-816b77d3c05b

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V) :
    ∀ {m n : Nat} {F : Forest V} {pref : List (Edge V)}
      {prefixTs : List ℝ} {top : ℝ} {ρ : (Edge V → ℝ) → ℝ},
      m ≤ n →
      allBranchesAnalytic choices n F pref prefixTs top ρ →
      allBranchesAnalytic choices m F pref prefixTs top ρ
  | 0, _n, _F, _pref, _prefixTs, _top, _ρ, _hle, _hanalytic => by
      trivial
  | m + 1, 0, _F, _pref, _prefixTs, _top, _ρ, hle, _hanalytic => by
      exact False.elim (Nat.not_succ_le_zero m hle)
  | m + 1, n + 1, F, pref, prefixTs, top, ρ, hle, hanalytic => by
      rcases hanalytic with ⟨hbound, hρ, hint, hstd, hrec, hchild⟩
      refine ⟨hbound, hρ, hint, hstd, hrec, ?_⟩
      intro e t ht
      exact
        solution choices
          (Nat.succ_le_succ_iff.mp hle) (hchild e t ht)
end BKAR.Forest
