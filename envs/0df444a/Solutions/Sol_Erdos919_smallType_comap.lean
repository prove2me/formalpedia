-- Prove2me | solution 1 for Erdos919.smallType_comap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:38:27.145873+00:00
-- url     : https://prove2.me/submissions/9819220f-8f93-4496-91f4-375013d18373

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_typeLT_image

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution {A B : Type u} [LinearOrder A] [WellFoundedLT A] [LinearOrder B]
    [WellFoundedLT B] (e : A ≃o B) {G : SimpleGraph B} {o : Ordinal.{u}}
    (h : ∀ X : Set B, typeLT X < o → ColorableOn G X ℕ) :
    ∀ Y : Set A, typeLT Y < o → ColorableOn (G.comap e) Y ℕ :=
  fun Y hY => ColorableOn.comap e (h _ (by rwa [typeLT_image]))
end Erdos919
