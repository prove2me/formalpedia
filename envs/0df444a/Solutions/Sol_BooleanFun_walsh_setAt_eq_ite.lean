-- Prove2me | solution 1 for BooleanFun.walsh_setAt_eq_ite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:09:48.097023+00:00
-- url     : https://prove2.me/submissions/17f76675-a7cc-4ae1-8a70-09bb293986db

import Definitions.Def_BooleanFun_Auxiliary
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.CharP.Pi
import Definitions.Def_BooleanFun_Basic
import Theorems.Thm_BooleanFun_setAt_other

set_option autoImplicit false
open BooleanFun
open Real BigOperators Function Finset Pi
open RealInnerProductSpace
noncomputable section
variable {α : Type*}
variable {n : ℕ} {f g : BooleanFunc n} {x y : Fin n → Fin 2} {i : Fin n}
variable {S S' : Finset (Fin n)} {v : Fin 2}
namespace BooleanFun
theorem _root_.solution : χ S (setAt i v x) = ite (i ∈ S) ((-1) ^ v.val * χ (S \ {i}) x) (χ S x) := by
  unfold walshCharacter
  split_ifs with h
  · rw [← mul_prod_erase S _ h, setAt_it, erase_eq]
    congr! 4 with j hj
    rw [setAt_other]
    rw [mem_sdiff, mem_singleton] at hj
    symm
    exact hj.right
  · congr! 3 with j hj
    rw [setAt_other]
    by_contra hc
    rw [hc] at h
    exact h hj
end BooleanFun
