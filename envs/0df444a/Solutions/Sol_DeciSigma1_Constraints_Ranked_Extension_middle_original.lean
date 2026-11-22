-- Prove2me | solution 1 for DeciSigma1.Constraints.Ranked.Extension.middle_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:04:07.559869+00:00
-- url     : https://prove2.me/submissions/8b430c79-8190-41d7-b278-cd71d07ff2e7

module
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_RankedExtensions
public import Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_not_source_original
public import Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_not_sink_original
public import Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_derives_into_source
public import Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_derives_out_of_sink

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
    {u v : Fin k} {w : Fin (k + m)}
    (hl : Derives ψ (Fin.castAdd m u) w)
    (hr : Derives ψ w (Fin.castAdd m v)) : ∃ t : Fin k, w = Fin.castAdd m t := by
  rcases e.variable_cases w with h | hs | ht
  · exact h
  · have he := e.derives_into_source hl hs
    exact False.elim (e.not_source_original u (he ▸ hs))
  · have he := e.derives_out_of_sink hr ht
    exact False.elim (e.not_sink_original v (he ▸ ht))
end Extension
end DeciSigma1.Constraints.Ranked
