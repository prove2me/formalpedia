-- Prove2me | solution 1 for DeciSigma1.Constraints.Ranked.Extension.upper_children
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:00:44.602922+00:00
-- url     : https://prove2.me/submissions/ef1799ef-4cce-4ea4-a8eb-a5e31ebd7f1a

module
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_RankedExtensions
public import Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_not_source_original

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
    {c : Fin (k + m)} {b : Fin n → Fin (k + m)} (h : LitT.leF c b ∈ ψ) (i : Fin n) :
    ¬ Source (b i) := by
  rcases e.upper _ _ h with ⟨c', b', _, rfl, rfl⟩ | ⟨hb, _⟩
  · exact e.not_source_original (b' i)
  · exact e.source_not_sink.mt (not_not.mpr (hb i).1)
end Extension
end DeciSigma1.Constraints.Ranked
