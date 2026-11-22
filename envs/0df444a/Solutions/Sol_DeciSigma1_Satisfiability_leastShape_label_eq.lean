-- Prove2me | solution 1 for DeciSigma1.Satisfiability.leastShape_label_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:25:03.38999+00:00
-- url     : https://prove2.me/submissions/d30221e0-27a1-4452-94b5-ac74521b6e98

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape
public import Theorems.Thm_DeciSigma1_Satisfiability_leastShape_fn

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}
namespace DeciSigma1.Satisfiability
theorem _root_.solution {π : List (Fin n)} {x : V} {a : Semantics.Sym}
    (h : (leastShape Γ x).fn π = some a) : a = shapeLabel Γ x π := by
  classical
  rw [leastShape_fn] at h
  split at h
  · exact (Option.some.inj h).symm
  · contradiction
end DeciSigma1.Satisfiability
