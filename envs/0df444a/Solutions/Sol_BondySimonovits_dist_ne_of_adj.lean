-- Prove2me | solution 1 for BondySimonovits.dist_ne_of_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:05:33.539267+00:00
-- url     : https://prove2.me/submissions/ba472a04-5329-4ce2-be26-24be24ac914d

module
public import Definitions.Def_BondySimonovitsLib_BSBasic
public import Definitions.Def_BondySimonovitsLib_BSLayers
public import Theorems.Thm_BondySimonovits_parity_walk

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} (K : SimpleGraph V)
namespace BondySimonovits
theorem _root_.solution (f : V → Bool) (hf : ∀ u v, K.Adj u v → f u ≠ f v) {x u v : V}
    (hr : K.Reachable x u) (h : K.Adj u v) : K.dist x u ≠ K.dist x v := by
  intro heq
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  obtain ⟨q, hq⟩ := (hr.trans h.reachable).exists_walk_length_eq_dist
  have h1 := parity_walk K f hf p
  have h2 := parity_walk K f hf q
  rw [hp] at h1
  rw [hq, ← heq] at h2
  have h3 := hf u v h
  revert h1 h2 h3
  cases f u <;> cases f v <;> cases f x <;> simp
end BondySimonovits
