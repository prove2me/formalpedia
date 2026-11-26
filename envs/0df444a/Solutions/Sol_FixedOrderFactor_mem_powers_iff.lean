-- Prove2me | solution 1 for FixedOrderFactor.mem_powers_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:00:06.509365+00:00
-- url     : https://prove2.me/submissions/73104a24-ad6c-4ce6-8315-36dd240447d1

module
public import Mathlib
public import Definitions.Def_FixedOrderFactor_Characters

set_option autoImplicit true
@[expose] public section
public section
open Finset
open FixedOrderFactor
variable (p : ℕ) [Fact p.Prime]
namespace FixedOrderFactor
theorem _root_.solution (r : ℕ) (u : (ZMod p)ˣ) :
    u ∈ powers p r ↔ ∃ c : ZMod p, c ≠ 0 ∧ (u : ZMod p) = c ^ r := by
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v, v.ne_zero, by simp⟩
  · rintro ⟨c, hc, h⟩
    refine ⟨Units.mk0 c hc, ?_⟩
    ext; simp [h]
end FixedOrderFactor
