-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.le_suffixLengthEnvelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:52:10.686121+00:00
-- url     : https://prove2.me/submissions/99b2291b-36e4-4ac8-ad2b-82155cad7461

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_cons
public import Theorems.Thm_DeciSigma1_Holes_Tail_le_iterate_of_le_self
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Words
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (m N : ℕ) :
    ∀ (Ss : List ℕ) (b : ℕ), b ≤ suffixLengthEnvelope m N Ss b
  | [] , b => le_rfl
  | S :: Ss, b => by
    rw [suffixLengthEnvelope_cons]
    have :=
        le_iterate_of_le_self (f := fun b => b + suffixLengthBound m N Ss b)
            (fun b => Nat.le_add_right _ _)
      S b
    exact (this.trans (Nat.le_add_right _ _)).trans (solution m N Ss _)
end DeciSigma1.Holes.Tail
