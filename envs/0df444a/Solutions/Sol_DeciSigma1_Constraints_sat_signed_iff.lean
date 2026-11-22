-- Prove2me | solution 1 for DeciSigma1.Constraints.sat_signed_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:37:01.412158+00:00
-- url     : https://prove2.me/submissions/1727d3dc-8301-4680-8af1-474163b62641

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Signed

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*}
namespace DeciSigma1.Constraints
theorem _root_.solution (c : Fin n → Bool) (A : (V × Bool) → Semantics.Tree n)
    (Γ : List (LitT n V)) :
    Covariant.Sat A (signed c Γ) ↔ ∀ l ∈ Γ, Covariant.Sat A (signedLit c l) := by
  constructor
  · intro h l hl m hm
    exact h m (List.mem_flatMap.mpr ⟨l, hl, hm⟩)
  · intro h m hm
    obtain ⟨l, hl, hm⟩ := List.mem_flatMap.mp hm
    exact h l hl m hm
end DeciSigma1.Constraints
