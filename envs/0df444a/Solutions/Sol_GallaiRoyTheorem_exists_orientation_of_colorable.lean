-- Prove2me | solution 1 for GallaiRoyTheorem.exists_orientation_of_colorable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:23:06.072941+00:00
-- url     : https://prove2.me/submissions/b1bdd4c5-1aa6-4562-a91e-617eec1c4ec4

module
public import Mathlib
public import Definitions.Def_GallaiRoyLib_GallaiRoy
public import Definitions.Def_GallaiRoy_Solution
public import Theorems.Thm_GallaiRoy_exists_orientation_of_colorable


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiRoyTheorem
variable {V : Type*}
namespace GallaiRoyTheorem
theorem _root_.solution (G : SimpleGraph V) (k : ℕ) (h : G.Colorable k) :
    ∃ o : V → V → Prop, IsOrientation G o ∧
      ∀ (m : ℕ) (f : Fin m → V), IsDirectedPath o f → m ≤ k :=
  GallaiRoy.exists_orientation_of_colorable G k h
end GallaiRoyTheorem
