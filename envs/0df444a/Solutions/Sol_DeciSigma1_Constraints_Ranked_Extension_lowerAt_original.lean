-- Prove2me | solution 1 for DeciSigma1.Constraints.Ranked.Extension.lowerAt_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:14:33.747699+00:00
-- url     : https://prove2.me/submissions/4fb8a5fe-4dfd-4fcf-bd55-93ed1269c21e

module
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_RankedExtensions
public import Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_lowerAt_reflect
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
    LowerAt ψ π (Fin.castAdd m u) (Fin.castAdd m v) ↔ LowerAt Γ π u v :=
  ⟨fun h => e.lowerAt_reflect h u v rfl rfl, fun h => h.map _ e.original_mem⟩
end Extension
end DeciSigma1.Constraints.Ranked
