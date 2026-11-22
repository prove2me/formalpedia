-- Prove2me | solution 1 for DeciSigma1.Constraints.Ranked.Extension.derives_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:12:18.532169+00:00
-- url     : https://prove2.me/submissions/aeb392cb-1328-43ee-859f-9a4711186e50

module
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_RankedExtensions
public import Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_derives_reflect
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
theorem _root_.solution (e : Extension Γ ψ Source Sink rank) (u v : Fin k) :
    Derives ψ (Fin.castAdd m u) (Fin.castAdd m v) ↔ Derives Γ u v :=
  ⟨fun h => e.derives_reflect h u v rfl rfl, fun h => h.map _ e.original_mem⟩
end Extension
end DeciSigma1.Constraints.Ranked
