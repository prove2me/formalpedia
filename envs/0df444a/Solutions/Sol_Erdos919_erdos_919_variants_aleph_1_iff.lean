-- Prove2me | solution 1 for Erdos919.erdos_919.variants.aleph_1_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:43:33.659804+00:00
-- url     : https://prove2.me/submissions/87684174-ae9d-4319-a7dd-1ac125d2ccc0

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_erdos919_aleph1_iff
public import Theorems.Thm_Erdos919_Q_aleph1_iff
public import Theorems.Thm_Erdos919_inc_iff

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
namespace Erdos919
namespace erdos_919.variants
theorem _root_.solution :
    (∃ G : SimpleGraph (ω_ 2 ^ 2 : Ordinal.{u}).ToType, G.chromaticCardinal = ℵ₁ ∧
      ∀ X : Set (ω_ 2 ^ 2 : Ordinal.{u}).ToType, typeLT X < ω_ 2 ^ 2 →
        (G.induce X).chromaticCardinal ≤ ℵ₀) ↔
    ∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ ℵ₀ < G.chromaticCardinal ∧
      ∀ (W : Set V) (_ : #W = ℵ₁), (G.induce W).chromaticCardinal ≤ ℵ₀ :=
  (Q_aleph1_iff.trans erdos919_aleph1_iff).trans inc_iff.symm
end erdos_919.variants
end Erdos919
