-- Prove2me | solution 1 for Erdos919.erdos_919.variants.aleph_2_imp_aleph_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:44:16.39783+00:00
-- url     : https://prove2.me/submissions/db54094b-cdfc-44af-8182-d177dc7f6c1b

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_mk_ulift_nat_le_aleph1
public import Theorems.Thm_Erdos919_erdos919_aleph2_iff
public import Theorems.Thm_Erdos919_erdos919_aleph1_iff
public import Theorems.Thm_Erdos919_Q_aleph2_iff
public import Theorems.Thm_Erdos919_Q_aleph1_iff

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
        (G.induce X).chromaticCardinal ≤ ℵ₀) →
    ∃ G : SimpleGraph (ω_ 2 ^ 2 : Ordinal.{u}).ToType, G.chromaticCardinal = ℵ₁ ∧
      ∀ X : Set (ω_ 2 ^ 2 : Ordinal.{u}).ToType, typeLT X < ω_ 2 ^ 2 →
        (G.induce X).chromaticCardinal ≤ ℵ₀ := by
  intro h
  obtain ⟨H, hH, hχ⟩ := erdos919_aleph2_iff.1 (Q_aleph2_iff.1 h)
  exact Q_aleph1_iff.2 (erdos919_aleph1_iff.2
    ⟨H, hH, ⟨fun c => (hχ _ mk_ulift_nat_le_aleph1).false (coloringULift c)⟩⟩)
end erdos_919.variants
end Erdos919
