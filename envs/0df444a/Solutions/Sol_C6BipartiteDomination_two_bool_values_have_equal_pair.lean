-- Prove2me | solution 1 for C6BipartiteDomination.two_bool_values_have_equal_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:49:29.866489+00:00
-- url     : https://prove2.me/submissions/6db68b7d-f2c2-4df3-aef7-f6d01f4759b1

import Definitions.Def_C6BipartiteDomination_A7
import Definitions.Def_C6BipartiteDomination_A8

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution (a b d : Bool) :
    a = b ∨ a = d ∨ b = d := by
  cases a <;> cases b <;> cases d <;> simp
end C6BipartiteDomination
