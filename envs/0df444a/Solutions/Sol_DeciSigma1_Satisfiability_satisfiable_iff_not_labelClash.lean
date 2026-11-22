-- Prove2me | solution 1 for DeciSigma1.Satisfiability.satisfiable_iff_not_labelClash
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:35:49.796097+00:00
-- url     : https://prove2.me/submissions/99669418-3bfa-4308-b43c-c571aef4768c

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape
public import Theorems.Thm_DeciSigma1_Satisfiability_leastShape_sat
public import Theorems.Thm_DeciSigma1_Constraints_LabelClash_unsatisfiable


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}
namespace DeciSigma1.Satisfiability
theorem _root_.solution : (∃ ρ, Covariant.Sat ρ Γ) ↔ ¬ LabelClash Γ :=
  ⟨fun hs hc => hc.unsatisfiable hs, fun hn => ⟨leastShape Γ, leastShape_sat hn⟩⟩
end DeciSigma1.Satisfiability
