-- Prove2me | solution 1 for Erdos919.Q_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:40:09.937143+00:00
-- url     : https://prove2.me/submissions/85737933-63fb-4748-8057-b7d977d8d0ec

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_induce_le_aleph0_iff
public import Theorems.Thm_Erdos919_chromaticCardinal_comap_equiv
public import Theorems.Thm_Erdos919_smallType_comap

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution (κ : Cardinal.{u}) :
    Q κ ↔ ∃ G : SimpleGraph (W.{u} ×ₗ W.{u}), SmallTypeCC G ∧ G.chromaticCardinal = κ := by
  constructor
  · rintro ⟨G, hχ, hX⟩
    exact ⟨G.comap isoV9.symm,
      smallType_comap isoV9.symm (fun X hXo => (induce_le_aleph0_iff G X).1 (hX X hXo)),
      (chromaticCardinal_comap_equiv isoV9.symm.toEquiv G).trans hχ⟩
  · rintro ⟨G, hG, hχ⟩
    exact ⟨G.comap isoV9, (chromaticCardinal_comap_equiv isoV9.toEquiv G).trans hχ,
      fun X hXo => (induce_le_aleph0_iff _ X).2 (smallType_comap isoV9 hG X hXo)⟩
end Erdos919
