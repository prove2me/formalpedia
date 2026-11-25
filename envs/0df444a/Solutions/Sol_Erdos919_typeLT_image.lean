-- Prove2me | solution 1 for Erdos919.typeLT_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:36:17.180568+00:00
-- url     : https://prove2.me/submissions/c2d2dab1-3eb8-4342-9ed1-29f1731530eb

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_typeLT_image_le

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution {A B : Type u} [LinearOrder A] [WellFoundedLT A] [LinearOrder B]
    [WellFoundedLT B] (e : A ≃o B) (X : Set A) : typeLT (e '' X) = typeLT X := by
  refine le_antisymm (typeLT_image_le e X) ?_
  have := typeLT_image_le e.symm (e '' X)
  rwa [e.symm_image_image] at this
end Erdos919
