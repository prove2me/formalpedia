-- Prove2me | solution 1 for Erdos919.size_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:38:24.579913+00:00
-- url     : https://prove2.me/submissions/2c6decac-0a78-42bb-9c44-0c4c515170c4

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_smallCard_comap
public import Theorems.Thm_Erdos919_mk_W
public import Theorems.Thm_Erdos919_smallCard_iff

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution (P : ∀ {V : Type u}, SimpleGraph V → Prop)
    (hP : ∀ {A B : Type u} (e : A ≃ B) (G : SimpleGraph B), P (G.comap e) ↔ P G) :
    (∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ P G ∧
      ∀ (X : Set V) (_ : #X = ℵ₁), (G.induce X).chromaticCardinal ≤ ℵ₀) ↔
    ∃ H : SimpleGraph W.{u}, SmallCardCC H ∧ P H := by
  constructor
  · rintro ⟨V, G, hV, hPG, hX⟩
    obtain ⟨e⟩ := Cardinal.eq.1 (hV.trans mk_W.symm)
    exact ⟨G.comap e.symm, smallCard_comap e.symm ((smallCard_iff hV G).2 hX),
      (hP e.symm G).2 hPG⟩
  · rintro ⟨H, hH, hPH⟩
    exact ⟨W, H, mk_W, hPH, (smallCard_iff mk_W H).1 hH⟩
end Erdos919
