-- Prove2me | solution 1 for DeciSigma1.Constraints.Ranked.Extension.cycle_reflect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:17:08.553157+00:00
-- url     : https://prove2.me/submissions/922dcdde-17c7-4845-ac1f-9903ab2d0f3e

module
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_RankedExtensions
public import Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_derives_original
public import Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_lowerAt_original
public import Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_upperAt_original
public import Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_cycle_original

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
    {π : List (Fin n)} {a b : Fin (k + m)} (hn : π ≠ []) (hl : LowerAt ψ π a a)
    (hd : Derives ψ a b) (hu : UpperAt ψ π b b) :
    ∃ u v : Fin k, LowerAt Γ π u u ∧ Derives Γ u v ∧ UpperAt Γ π v v := by
  obtain ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩ := e.cycle_original hn hl hd hu
  exact ⟨u, v, (e.lowerAt_original ..).mp hl, (e.derives_original ..).mp hd,
    (e.upperAt_original ..).mp hu⟩
end Extension
end DeciSigma1.Constraints.Ranked
