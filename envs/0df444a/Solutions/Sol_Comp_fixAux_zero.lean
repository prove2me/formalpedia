-- Prove2me | solution 1 for Comp.fixAux_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:41:58.00928+00:00
-- url     : https://prove2.me/submissions/c4776e38-189c-4c78-9e07-90484f6c641c

import Definitions.Def_Comp_Lattice
import Mathlib.Data.Fintype.Card
import Definitions.Def_Comp_FixLoop

set_option autoImplicit true
open Comp
variable {S : Type*} [DecidableEq S]
namespace Comp
theorem _root_.solution (f : Finset S → Finset S) (x : Finset S) : fixAux f 0 x = x := rfl
end Comp
