-- Prove2me | solution 1 for Erdos919.bigGraph_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:39:04.782096+00:00
-- url     : https://prove2.me/submissions/9be2a480-2bb4-4a86-b713-db2a33272f38

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_blowup_lower
public import Theorems.Thm_Erdos919_exists_unbounded_fiber

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution {H : SimpleGraph W.{u}} {α : Type u} (hα : #α ≤ ℵ₁)
    (c : (bigGraph H).Coloring α) : Nonempty (H.Coloring α) :=
  blowup_lower (exists_unbounded_fiber hα) (coloringOfComap ofLex c)
end Erdos919
