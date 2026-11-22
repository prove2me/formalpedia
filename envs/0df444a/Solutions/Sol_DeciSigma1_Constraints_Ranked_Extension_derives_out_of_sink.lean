-- Prove2me | solution 1 for DeciSigma1.Constraints.Ranked.Extension.derives_out_of_sink
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:01:53.521645+00:00
-- url     : https://prove2.me/submissions/562547d4-9328-4b78-9c36-1ebcdfd9fd1e

module
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_RankedExtensions
public import Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_not_sink_original
public import Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_lower_children

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
    {a b : Fin (k + m)} (h : Derives ψ a b) (ha : Sink a) : b = a := by
  induction h with
  | refl => rfl
  | lit hl =>
    obtain ⟨a, _, _, rfl, _⟩ := e.copy _ _ hl
    exact False.elim (e.not_sink_original a ha)
  | trans _ _ ih ih' =>
    have he := ih ha
    exact (ih' (he ▸ ha)).trans he
  | decomp i hl _ _ => exact False.elim (e.lower_children hl i ha)
end Extension
end DeciSigma1.Constraints.Ranked
