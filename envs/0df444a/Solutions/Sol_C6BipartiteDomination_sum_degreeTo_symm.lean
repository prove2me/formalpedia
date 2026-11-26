-- Prove2me | solution 1 for C6BipartiteDomination.sum_degreeTo_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:47:37.162819+00:00
-- url     : https://prove2.me/submissions/96571bc7-7ca0-4cee-a194-053892f2be80

import Definitions.Def_C6BipartiteDomination_A5
import Definitions.Def_C6BipartiteDomination_A6
import Theorems.Thm_C6BipartiteDomination_degreeTo_as_sum

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution (A B : Finset V) :
    (∑ a ∈ A, degreeTo G B a) = ∑ b ∈ B, degreeTo G A b := by
  classical
  simp_rw [degreeTo_as_sum]
  rw [Finset.sum_comm]
  simp_rw [G.adj_comm]
end C6BipartiteDomination
