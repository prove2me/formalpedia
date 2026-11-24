-- Prove2me | solution 1 for FairChores.cbarSum_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:23:04.187159+00:00
-- url     : https://prove2.me/submissions/2a500507-5b76-4f33-98e7-cbc2e03aacfb

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresBagLemma
import Theorems.Thm_FairChores_cbarSum_empty
attribute [local simp] FairChores.cbarSum_empty



set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
variable (c : Fin n → T → ℝ) (p : T → ℝ) (mu : Fin n → ℝ)
omit [Fintype T]
namespace FairChores
theorem _root_.solution {ci p : T → ℝ} {X : Finset T} {t : T} (ht : t ∉ X) :
    cbarSum ci p (insert t X) = cbar ci p t + cbarSum ci p X := by
  simp [cbarSum, Finset.sum_insert ht]
end FairChores
