-- Prove2me | solution 1 for Erdos919.typeLT_image_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:35:27.881717+00:00
-- url     : https://prove2.me/submissions/ecbdeb93-e43c-4230-8292-47311d6a5981

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
namespace Erdos919
theorem _root_.solution {A B : Type u} [LinearOrder A] [WellFoundedLT A] [LinearOrder B]
    [WellFoundedLT B] (e : A ≃o B) (X : Set A) : typeLT (e '' X) ≤ typeLT X := by
  have hmem : ∀ y : e '' X, e.symm y.1 ∈ X := by
    rintro ⟨_, x, hx, rfl⟩
    simpa using hx
  exact type_le_iff'.2 ⟨(OrderEmbedding.ofStrictMono
    (fun y : e '' X => (⟨e.symm y.1, hmem y⟩ : X)) (fun _ _ h => e.symm.strictMono h)).ltEmbedding⟩
end Erdos919
