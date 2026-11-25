-- Prove2me | solution 1 for Erdos919.erdos_919.variants.aleph_1_of_CH
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:45:04.611955+00:00
-- url     : https://prove2.me/submissions/c4d61536-d9c1-4f3f-8417-88f775a834aa

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_erdos919_aleph1_of_CH
public import Theorems.Thm_Erdos919_Q_aleph1_iff
public import Theorems.Thm_Erdos919_continuum_eq_aleph1_zero

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
namespace Erdos919
namespace erdos_919.variants
theorem _root_.solution (hCH : 𝔠 = ℵ₁) :
    ∃ G : SimpleGraph (ω_ 2 ^ 2 : Ordinal.{u}).ToType, G.chromaticCardinal = ℵ₁ ∧
      ∀ X : Set (ω_ 2 ^ 2 : Ordinal.{u}).ToType, typeLT X < ω_ 2 ^ 2 →
        (G.induce X).chromaticCardinal ≤ ℵ₀ := by
  exact Q_aleph1_iff.2 (erdos919_aleph1_of_CH (continuum_eq_aleph1_zero hCH))
end erdos_919.variants
end Erdos919
