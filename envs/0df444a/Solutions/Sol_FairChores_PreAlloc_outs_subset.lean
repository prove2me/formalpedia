-- Prove2me | solution 1 for FairChores.PreAlloc.outs_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:22:47.015795+00:00
-- url     : https://prove2.me/submissions/9067ffab-bf40-4cb6-b402-d06971484fbf

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
    (h : P.Splits p A R) : P.outs ⊆ R := by
  intro t ht
  rw [← h.2.2.2.2.2.1]
  exact Finset.mem_union_left _ ht
end PreAlloc
end FairChores
