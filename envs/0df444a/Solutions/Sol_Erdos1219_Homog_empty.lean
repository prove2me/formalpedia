-- Prove2me | solution 1 for Erdos1219.Homog.empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:43:15.0278+00:00
-- url     : https://prove2.me/submissions/42894961-c197-46e4-b449-c4db4667c195

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
theorem _root_.solution (f : V → V → Bool) (c : Bool) : Homog f c ∅ := by
  intro x hx; simp at hx
end Homog
end Erdos1219
