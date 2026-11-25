-- Prove2me | solution 1 for Erdos919.diffColor_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:34:27.42521+00:00
-- url     : https://prove2.me/submissions/0e6efc2b-5310-44c0-8310-6055fce9917e

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
variable (I : Type*) [LinearOrder I]
variable {I}
namespace Erdos919
theorem _root_.solution {T : Type*} [LinearOrder T] [WellFoundedLT T] [Inhabited T]
    {x y z : T → Bool} (hxy : x ≠ y) (hyz : y ≠ z) : diffColor x y ≠ diffColor y z := by
  classical
  have h1 : ∃ t, x t ≠ y t := Function.ne_iff.1 hxy
  have h2 : ∃ t, y t ≠ z t := Function.ne_iff.1 hyz
  unfold diffColor
  rw [dif_pos h1, dif_pos h2]
  intro h
  obtain ⟨ht, hb⟩ := Prod.ext_iff.1 h
  have hm := WellFounded.min_mem wellFounded_lt {t | x t ≠ y t} h1
  exact hm (hb.trans (congrArg y ht.symm))
end Erdos919
