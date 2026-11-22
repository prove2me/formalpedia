-- Prove2me | solution 1 for DeciSigma1.Full.Closure.leaf_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:41:38.811306+00:00
-- url     : https://prove2.me/submissions/c813dda2-ca1b-43fd-b749-9a270cada930

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
public import Theorems.Thm_DeciSigma1_Full_Models_mem_nonBottomPrefixes_of_hasTopPrefix


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Full.Models DeciSigma1.Semantics
variable {n : ℕ}
namespace DeciSigma1.Full.Closure
theorem _root_.solution (c : Fin n → Bool) (t : Semantics.Tree n) (w : List (Fin n)) :
    w ∈ leaf c t false → w ∈ leaf c t true → False := by
  intro hp hm
  exact (leaf_minus c t w).mp hm (mem_nonBottomPrefixes_of_hasTopPrefix _ _ hp)
end DeciSigma1.Full.Closure
