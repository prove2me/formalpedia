-- Prove2me | solution 1 for DeciSigma1.Constraints.Ranked.Extension.upperAt_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:14:50.7528+00:00
-- url     : https://prove2.me/submissions/347e64fb-e1db-4414-835a-73c834195122

module
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_RankedExtensions
public import Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_upperAt_reflect
public import Theorems.Thm_DeciSigma1_Constraints_UpperAt_map


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Constraints.Ranked
variable {n k m : ℕ}
variable {Γ : List (LitT n (Fin k))} {ψ : List (LitT n (Fin (k + m)))}
  {Source Sink : Fin (k + m) → Prop} {rank : Fin (k + m) → ℕ}
namespace DeciSigma1.Constraints.Ranked
namespace Extension
theorem _root_.solution (e : Extension Γ ψ Source Sink rank)
    (π : List (Fin n)) (u v : Fin k) :
    UpperAt ψ π (Fin.castAdd m u) (Fin.castAdd m v) ↔ UpperAt Γ π u v :=
  ⟨fun h => e.upperAt_reflect h u v rfl rfl, fun h => h.map _ e.original_mem⟩
end Extension
end DeciSigma1.Constraints.Ranked
