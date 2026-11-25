-- Prove2me | solution 1 for Erdos919.erdos_919.variants.iff_erdos_918_i
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:44:15.851551+00:00
-- url     : https://prove2.me/submissions/b14049d7-fecf-4394-87ae-4a81534f2bc9

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_erdos919_aleph2_iff
public import Theorems.Thm_Erdos919_Q_aleph2_iff
public import Theorems.Thm_Erdos919_e918_iff

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
namespace Erdos919
namespace erdos_919.variants
theorem _root_.solution :
    (∃ G : SimpleGraph (ω_ 2 ^ 2 : Ordinal.{u}).ToType, G.chromaticCardinal = ℵ_ 2 ∧
      ∀ X : Set (ω_ 2 ^ 2 : Ordinal.{u}).ToType, typeLT X < ω_ 2 ^ 2 →
        (G.induce X).chromaticCardinal ≤ ℵ₀) ↔
    ∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ G.chromaticCardinal = ℵ_ 2 ∧
      ∀ (W : Set V) (_ : #W = ℵ₁), (G.induce W).chromaticCardinal ≤ ℵ₀ :=
  (Q_aleph2_iff.trans erdos919_aleph2_iff).trans e918_iff.symm
end erdos_919.variants
end Erdos919
