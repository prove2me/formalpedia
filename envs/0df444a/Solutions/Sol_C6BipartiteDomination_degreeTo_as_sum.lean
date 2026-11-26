-- Prove2me | solution 1 for C6BipartiteDomination.degreeTo_as_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:46:05.358875+00:00
-- url     : https://prove2.me/submissions/52574bcf-634d-4d51-b92c-e463dd8af641

import Definitions.Def_C6BipartiteDomination_A5
import Definitions.Def_C6BipartiteDomination_A6

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
open Classical
namespace C6BipartiteDomination
theorem _root_.solution (A : Finset V) (v : V) :
    degreeTo G A v = ∑ u ∈ A, if G.Adj v u then 1 else 0 := by
  classical
  unfold degreeTo
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
end C6BipartiteDomination
