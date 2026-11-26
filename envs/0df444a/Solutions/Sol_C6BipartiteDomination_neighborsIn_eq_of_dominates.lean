-- Prove2me | solution 1 for C6BipartiteDomination.neighborsIn_eq_of_dominates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:43:02.796536+00:00
-- url     : https://prove2.me/submissions/84b123cc-2c24-4182-b5b9-bbcaca18e14d

import Definitions.Def_C6BipartiteDomination_A2
import Definitions.Def_C6BipartiteDomination_A3
import Theorems.Thm_C6BipartiteDomination_mem_neighborsIn
import Theorems.Thm_C6BipartiteDomination_neighborsIn_self_subset

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D W : Finset V}
    (hdom : ∀ ⦃w⦄, w ∈ W → ∃ d ∈ D, G.Adj d w) :
    neighborsIn G D W = W := by
  classical
  ext w
  constructor
  · intro hw
    exact neighborsIn_self_subset G D W hw
  · intro hw
    rw [mem_neighborsIn]
    obtain ⟨d, hd, hadj⟩ := hdom hw
    exact ⟨hw, d, hd, hadj⟩
end C6BipartiteDomination
