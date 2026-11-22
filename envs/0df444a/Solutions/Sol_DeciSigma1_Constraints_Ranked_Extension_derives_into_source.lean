-- Prove2me | solution 1 for DeciSigma1.Constraints.Ranked.Extension.derives_into_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:01:41.424549+00:00
-- url     : https://prove2.me/submissions/0d51f222-f2a5-49ab-8241-c7139f4a34f7

module
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_RankedExtensions
public import Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_not_source_original
public import Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_upper_children

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
    {a b : Fin (k + m)} (h : Derives ψ a b) (hb : Source b) : a = b := by
  induction h with
  | refl => rfl
  | lit hl =>
    obtain ⟨_, b, _, _, rfl⟩ := e.copy _ _ hl
    exact False.elim (e.not_source_original b hb)
  | trans _ _ ih ih' =>
    have he := ih' hb
    exact (ih (he ▸ hb)).trans he
  | decomp i _ _ hu => exact False.elim (e.upper_children hu i hb)
end Extension
end DeciSigma1.Constraints.Ranked
