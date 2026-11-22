-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.take_drop_deleteSites
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:26:00.124596+00:00
-- url     : https://prove2.me/submissions/736cecdd-d6e9-4b14-bf25-c92f7b24c275

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
public import Theorems.Thm_DeciSigma1_Holes_Fresh_isJunction_of_mem
public import Theorems.Thm_DeciSigma1_Words_take_drop_deletePositions


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {δ : ℕ} {cs : Finset ℕ}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {α : Type} (x : List α) {a n : ℕ}
    (hfree : ∀ J, IsJunction δ cs J → ¬ (a < J ∧ J < a + n)) :
    ((deletePositions x (sitePositions δ cs)).drop a).take n =
      (x.drop (greatestPreimage (sitePositions δ cs) a)).take n :=
  take_drop_deletePositions x fun _ hp => hfree _ (isJunction_of_mem hp)
end DeciSigma1.Holes.Fresh
