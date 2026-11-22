-- Prove2me | solution 1 for DeciSigma1.Constraints.lowerF_iff_lits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:31:12.066573+00:00
-- url     : https://prove2.me/submissions/19c01129-04ec-4969-88a8-b2717c762333

module
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*}
namespace DeciSigma1.Constraints
theorem _root_.solution (Γ : List (LitT n V)) (x : V) :
    LowerF Γ x ↔ ∃ l ∈ lowerLits Γ, Derives Γ l.2 x := by
  constructor
  · rintro ⟨a, u, hl, hd⟩
    exact ⟨(a, u), (mem_lowerLits Γ a u).mpr hl, hd⟩
  · rintro ⟨⟨a, u⟩, hl, hd⟩
    exact ⟨a, u, (mem_lowerLits Γ a u).mp hl, hd⟩
end DeciSigma1.Constraints
