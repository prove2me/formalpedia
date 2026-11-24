-- Prove2me | solution 1 for FairChores.wtSum_sdiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:20:51.202803+00:00
-- url     : https://prove2.me/submissions/bec33768-82a7-460a-9de1-52826c42869b

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Theorems.Thm_FairChores_cbarSum_empty
attribute [local simp] FairChores.cbarSum_empty

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ} {mu : ℝ}
omit [Fintype T]
namespace FairChores
theorem _root_.solution {A B : Finset T} (h : A ⊆ B) :
    wtSum c p mu B = wtSum c p mu (B \ A) + wtSum c p mu A := by
  simp only [wtSum]
  rw [← Finset.sum_sdiff h]
end FairChores
