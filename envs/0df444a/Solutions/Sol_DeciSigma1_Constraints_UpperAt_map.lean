-- Prove2me | solution 1 for DeciSigma1.Constraints.UpperAt.map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:20:24.981842+00:00
-- url     : https://prove2.me/submissions/0c7d5213-4a92-4e89-8f6d-ef90d89adab2

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
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}
namespace DeciSigma1.Constraints
namespace UpperAt
theorem _root_.solution {W : Type*} {ψ : List (LitT n W)} (r : V → W)
    (hr : ∀ l ∈ Γ, l.map r ∈ ψ) {π : List (Fin n)} {a b : V}
    (h : UpperAt Γ π a b) : UpperAt ψ π (r a) (r b) := by
  induction h with
  | nil hd => exact .nil (hd.map r hr)
  | @cons x z c y π i hd hl _ ih =>
    exact UpperAt.cons (b := r ∘ c) (hd.map r hr) (hr _ hl) ih
end UpperAt
end DeciSigma1.Constraints
