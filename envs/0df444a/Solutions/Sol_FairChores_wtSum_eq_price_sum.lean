-- Prove2me | solution 1 for FairChores.wtSum_eq_price_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:23:36.758169+00:00
-- url     : https://prove2.me/submissions/b7f30c37-e63f-4694-b575-b7d655f8cc2a

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresPreAlloc
import Definitions.Def_RequestProject_ChoresBagLemma
import Definitions.Def_RequestProject_ChoresBagFilling
import Theorems.Thm_FairChores_cbarSum_empty
attribute [local simp] FairChores.cbarSum_empty



set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
variable {c : Fin n → T → ℝ} {p : T → ℝ} {mu : Fin n → ℝ}
omit [Fintype T] [DecidableEq T]
namespace FairChores
theorem _root_.solution {i : Fin n} {R : Finset T} (h : ∀ t ∈ R, mu i < cbar (c i) p t) :
    wtSum (c i) p (mu i) R = ∑ t ∈ R, p t := by
  refine Finset.sum_congr rfl fun t ht => ?_
  simp [wt, h t ht]
end FairChores
