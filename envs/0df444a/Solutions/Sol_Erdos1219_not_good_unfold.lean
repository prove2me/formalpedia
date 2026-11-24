-- Prove2me | solution 1 for Erdos1219.not_good_unfold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:44:37.162799+00:00
-- url     : https://prove2.me/submissions/e45c72fc-d462-4b12-84b2-b97be8b7ad0f

import Definitions.Def_Erdos1219_Defs
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_Erdos1219_UnbalancedErdosRado

set_option autoImplicit false
open Cardinal Ordinal Set
open Erdos1219
universe u
variable {W : Type u} [LinearOrder W] [WellFoundedLT W]
omit [WellFoundedLT W]
namespace Erdos1219
theorem _root_.solution {f : W → W → Bool} {c : Bool} {μ : Cardinal.{u}} {α : W}
    (hα : α ∈ bigCof μ) (hno : ¬ IsGood f c μ α) :
    ∃ (Z : Set W) (β : W), Z ⊆ nbr f c α ∧ Homog f (!c) Z ∧ #Z ≤ μ ∧ β < α ∧ Z ⊆ Iio β ∧
      nbr f c α ∩ common f c Z ⊆ Iio β := by
  unfold IsGood at hno
  push Not at hno
  obtain ⟨Z, hZA, hZh, hZμ, β, hβα, hZβ, hγ⟩ := hno hα
  exact ⟨Z, β, hZA, hZh, hZμ, hβα, hZβ, fun γ hγ' => hγ γ hγ'⟩
end Erdos1219
