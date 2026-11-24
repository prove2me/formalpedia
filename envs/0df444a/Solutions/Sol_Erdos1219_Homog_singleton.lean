-- Prove2me | solution 1 for Erdos1219.Homog.singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:44:37.801796+00:00
-- url     : https://prove2.me/submissions/002009a8-3a1e-4534-94a1-72c21be48bd1

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
theorem _root_.solution (f : V → V → Bool) (c : Bool) (x : V) : Homog f c {x} := by
  intro a ha b hb hab
  simp only [Set.mem_singleton_iff] at ha hb
  exact absurd (ha.trans hb.symm) hab
end Homog
end Erdos1219
