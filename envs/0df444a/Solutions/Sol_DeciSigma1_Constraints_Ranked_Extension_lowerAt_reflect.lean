-- Prove2me | solution 1 for DeciSigma1.Constraints.Ranked.Extension.lowerAt_reflect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:13:24.941511+00:00
-- url     : https://prove2.me/submissions/833682ea-1d12-46a1-a946-e994220a1687

module
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_RankedExtensions
public import Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_not_source_original
public import Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_derives_original
public import Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_lowerAt_source

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
    {π : List (Fin n)} {a b : Fin (k + m)} (h : LowerAt ψ π a b) :
    ∀ u v : Fin k, a = Fin.castAdd m u → b = Fin.castAdd m v → LowerAt Γ π u v := by
  induction h with
  | nil hd =>
    rintro u v rfl rfl
    exact .nil ((e.derives_original _ _).mp hd)
  | @cons c z b a π i hl hd hp ih =>
    rintro u v rfl rfl
    rcases e.lower _ _ hl with ⟨c', z', hl', rfl, rfl⟩ | ⟨hc, _⟩
    · exact LowerAt.cons hl' ((e.derives_original _ _).mp hd) (ih _ _ rfl rfl)
    · exact False.elim (e.not_source_original u (e.lowerAt_source hp (hc i).1).1)
end Extension
end DeciSigma1.Constraints.Ranked
