-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.greatestPreimage_add_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:28:23.411921+00:00
-- url     : https://prove2.me/submissions/3746e1a9-a882-4492-a342-1aa37a32570b

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
public import Theorems.Thm_DeciSigma1_Holes_Fresh_pred_not_mem_sitePositions
public import Theorems.Thm_DeciSigma1_Holes_Fresh_isJunction_of_mem
public import Theorems.Thm_DeciSigma1_Words_eq_of_retainedCount_eq
public import Theorems.Thm_DeciSigma1_Words_not_mem_of_no_junction
public import Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage_add


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {δ : ℕ} {cs : Finset ℕ}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {a n p : ℕ} (hn : 0 < n)
    (hfree : ∀ J, IsJunction δ cs J → ¬ (a < J ∧ J < a + n)) (hp : Retained δ cs p)
    (hpr : ∀ c ∈ cs, p ≠ c + δ) (hk : retainedCount (sitePositions δ cs) p = a + n) :
    greatestPreimage (sitePositions δ cs) a + n = p := by
  have hret := not_mem_of_no_junction fun q hq => hfree _ (isJunction_of_mem hq)
  refine eq_of_retainedCount_eq (by rw [retainedCount_greatestPreimage_add hret, hk]) (Or.inr ?_)
    (pred_not_mem_sitePositions hp hpr)
  rw [show greatestPreimage (sitePositions δ cs) a + n - 1 = greatestPreimage
      (sitePositions δ cs) a + (n - 1)
    by omega]
  exact hret (n - 1) (by omega)
end DeciSigma1.Holes.Fresh
