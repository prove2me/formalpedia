-- Prove2me | solution 1 for DeciSigma1.Constraints.holdsT_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:36:40.328798+00:00
-- url     : https://prove2.me/submissions/85f8dd23-b9a6-4aa0-8d01-301b2f363a38

module
public import Mathlib.Data.Fintype.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Semantics
variable {n : ℕ}
namespace DeciSigma1.Constraints
theorem _root_.solution {V W : Type*} (c : Fin n → Bool)
    (f : V → W) (ρ : W → Semantics.Tree n) (l : LitT n V) :
    HoldsT c ρ (l.map f) ↔ HoldsT c (ρ ∘ f) l := by cases l <;> rfl
end DeciSigma1.Constraints
