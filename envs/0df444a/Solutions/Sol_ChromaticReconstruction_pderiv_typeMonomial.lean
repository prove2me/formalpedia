-- Prove2me | solution 1 for ChromaticReconstruction.pderiv_typeMonomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:51:32.43785+00:00
-- url     : https://prove2.me/submissions/3bd95b85-a37e-44e3-91d0-730714222e72

import Definitions.Def_RequestProject_LeafExtMaster
import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_Uniform
import Theorems.Thm_ChromaticReconstruction_pderiv_prod


set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution (A : Set (Sym2 V)) (r : ℕ) :
    pderiv r (typeMonomial A) = ∑ C0 ∈ compSets A,
      if C0.card = r then ∏ C ∈ (compSets A).erase C0, (X C.card : MvPolynomial ℕ ℚ) else 0 := by
  unfold typeMonomial
  rw [pderiv_prod]
  refine sum_congr rfl fun C0 _ => ?_
  rw [pderiv_X]
  by_cases h : C0.card = r
  · subst h
    rw [if_pos rfl, Pi.single_eq_same, mul_one]
    convert rfl
  · rw [if_neg h, Pi.single_eq_of_ne h, mul_zero]
end ChromaticReconstruction
