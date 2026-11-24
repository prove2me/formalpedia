-- Prove2me | solution 1 for Erdos1219.Homog.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:39:58.444228+00:00
-- url     : https://prove2.me/submissions/cfd8c1d3-fe6f-4290-8902-337413a78389

import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Data.Finset.Card
import Definitions.Def_Erdos1219_Defs

set_option autoImplicit false
open Cardinal
open Erdos1219
universe u
variable {V : Type u}
namespace Erdos1219
namespace Homog
theorem _root_.solution {f : V → V → Bool} {c : Bool} {H H' : Set V} (h : Homog f c H)
    (hH : H' ⊆ H) : Homog f c H' :=
  fun x hx y hy hxy => h x (hH hx) y (hH hy) hxy
end Homog
end Erdos1219
