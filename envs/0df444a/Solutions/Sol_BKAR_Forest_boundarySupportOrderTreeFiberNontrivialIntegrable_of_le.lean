-- Prove2me | solution 1 for BKAR.Forest.boundarySupportOrderTreeFiberNontrivialIntegrable_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:48:41.456262+00:00
-- url     : https://prove2.me/submissions/a7ace997-adbc-430e-9d5c-a10c8aeadcd2

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers

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
      boundarySupportOrderTreeFiberNontrivialIntegrable choices n
        F pref prefixTs top ρ →
      boundarySupportOrderTreeFiberNontrivialIntegrable choices m
        F pref prefixTs top ρ
  | 0, _n, _F, _pref, _prefixTs, _top, _ρ, _hle, _hfiber => by
      trivial
  | m + 1, 0, _F, _pref, _prefixTs, _top, _ρ, hle, _hfiber => by
      exact False.elim (Nat.not_succ_le_zero m hle)
  | m + 1, n + 1, F, pref, prefixTs, top, ρ, hle, hfiber => by
      rcases hfiber with ⟨hInt, hchild⟩
      refine ⟨hInt, ?_⟩
      intro e t ht
      exact
        solution choices
          (Nat.succ_le_succ_iff.mp hle) (hchild e t ht)
end BKAR.Forest
