-- Prove2me | solution 1 for Erdos919.erdos919_aleph2_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:42:24.223445+00:00
-- url     : https://prove2.me/submissions/1d763955-fc7b-44ad-b3e6-040cefb22790

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_smallCard_comap
public import Theorems.Thm_Erdos919_equiv_lex
public import Theorems.Thm_Erdos919_bigGraph_smallType
public import Theorems.Thm_Erdos919_smallCard_of_smallType
public import Theorems.Thm_Erdos919_bigGraph_lower

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution :
    (∃ G : SimpleGraph (W.{u} ×ₗ W.{u}), SmallTypeCC G ∧ ChiAleph2 G) ↔
      ∃ H : SimpleGraph W.{u}, SmallCardCC H ∧ ChiAleph2 H := by
  constructor
  · rintro ⟨G, hG, hχ⟩
    obtain ⟨e⟩ := equiv_lex.{u}
    exact ⟨G.comap e, smallCard_comap e (smallCard_of_smallType hG),
      fun α hα => ⟨fun c => (hχ α hα).false (coloringOfComap e c)⟩⟩
  · rintro ⟨H, hH, hχ⟩
    refine ⟨bigGraph H, bigGraph_smallType H hH, fun α hα => ⟨fun c => ?_⟩⟩
    obtain ⟨d⟩ := bigGraph_lower hα c
    exact (hχ α hα).false d
end Erdos919
