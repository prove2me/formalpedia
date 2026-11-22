-- Prove2me | solution 1 for DeciSigma1.Constraints.Ranked.Extension.upperAt_reflect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:13:27.361807+00:00
-- url     : https://prove2.me/submissions/22f4eeb3-4a0d-4214-b129-0a8284778721

module
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_RankedExtensions
public import Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_not_sink_original
public import Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_derives_original
public import Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_upperAt_sink

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
    {π : List (Fin n)} {a b : Fin (k + m)} (h : UpperAt ψ π a b) :
    ∀ u v : Fin k, a = Fin.castAdd m u → b = Fin.castAdd m v → UpperAt Γ π u v := by
  induction h with
  | nil hd =>
    rintro u v rfl rfl
    exact .nil ((e.derives_original _ _).mp hd)
  | @cons a z c b π i hd hl hp ih =>
    rintro u v rfl rfl
    rcases e.upper _ _ hl with ⟨z', c', hl', rfl, rfl⟩ | ⟨hc, _⟩
    · exact UpperAt.cons ((e.derives_original _ _).mp hd) hl' (ih _ _ rfl rfl)
    · exact False.elim (e.not_sink_original v (e.upperAt_sink hp (hc i).1).1)
end Extension
end DeciSigma1.Constraints.Ranked
