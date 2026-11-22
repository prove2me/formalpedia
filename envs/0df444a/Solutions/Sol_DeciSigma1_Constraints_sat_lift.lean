-- Prove2me | solution 1 for DeciSigma1.Constraints.sat_lift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:52:38.719796+00:00
-- url     : https://prove2.me/submissions/89d10799-60c2-49b7-a18d-32282ad5bb1f

module
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_RankedExtensions
public import Theorems.Thm_DeciSigma1_Constraints_sat_rename


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n k m : ℕ}
namespace DeciSigma1.Constraints
theorem _root_.solution (ρ' : Fin (k + m) → Semantics.Tree n) (Γ : List (LitT n (Fin k))) :
    Covariant.Sat ρ' (lift Γ m) ↔ Covariant.Sat (ρ' ∘ Fin.castAdd m) Γ :=
  sat_rename _ _ _
end DeciSigma1.Constraints
