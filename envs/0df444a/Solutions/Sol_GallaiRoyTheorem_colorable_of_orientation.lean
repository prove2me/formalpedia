-- Prove2me | solution 1 for GallaiRoyTheorem.colorable_of_orientation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:21:22.63857+00:00
-- url     : https://prove2.me/submissions/af523c9f-0340-4246-9d49-97aef27a6b85

module
public import Mathlib
public import Definitions.Def_GallaiRoyLib_GallaiRoy
public import Definitions.Def_GallaiRoy_Solution
public import Theorems.Thm_GallaiRoy_colorable_of_orientation


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiRoyTheorem
variable {V : Type*}
namespace GallaiRoyTheorem
theorem _root_.solution [Finite V] (G : SimpleGraph V) (o : V → V → Prop)
    (ho : IsOrientation G o) (k : ℕ)
    (hk : ∀ (m : ℕ) (f : Fin m → V), IsDirectedPath o f → m ≤ k) : G.Colorable k :=
  GallaiRoy.colorable_of_orientation G o ho k hk
end GallaiRoyTheorem
