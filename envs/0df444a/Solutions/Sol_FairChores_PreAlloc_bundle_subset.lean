-- Prove2me | solution 1 for FairChores.PreAlloc.bundle_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:22:41.202805+00:00
-- url     : https://prove2.me/submissions/c6280156-4e71-405e-bfcc-5dd1f07115a6

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresPreAlloc

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
omit [Fintype T]
namespace FairChores
namespace PreAlloc
theorem _root_.solution {P : PreAlloc T n} {p : T → ℝ} {A : Finset (Fin n)} {R : Finset T}
    (h : P.Splits p A R) (i : Fin n) : P.bundle i ⊆ R := by
  intro t ht
  rw [← h.2.2.2.2.2.1]
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ht⟩)
end PreAlloc
end FairChores
