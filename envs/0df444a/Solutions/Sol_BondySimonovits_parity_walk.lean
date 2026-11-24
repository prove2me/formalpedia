-- Prove2me | solution 1 for BondySimonovits.parity_walk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:04:15.010934+00:00
-- url     : https://prove2.me/submissions/d45a3122-6a04-4256-a455-c0e368368876

module
public import Definitions.Def_BondySimonovitsLib_BSBasic
public import Definitions.Def_BondySimonovitsLib_BSLayers

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} (K : SimpleGraph V)
namespace BondySimonovits
theorem _root_.solution (f : V → Bool) (hf : ∀ u v, K.Adj u v → f u ≠ f v) :
    ∀ {u v : V} (p : K.Walk u v), (f v = f u ↔ Even p.length) := by
  intro u v p
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    rw [Walk.length_cons, Nat.even_add_one, ← ih]
    have := hf _ _ h
    revert this ih
    cases f a <;> cases f b <;> cases f c <;> simp
end BondySimonovits
