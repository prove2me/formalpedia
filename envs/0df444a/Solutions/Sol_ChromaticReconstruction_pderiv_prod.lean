-- Prove2me | solution 1 for ChromaticReconstruction.pderiv_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:46:19.961968+00:00
-- url     : https://prove2.me/submissions/1e3669df-943f-4766-9e2f-750815225007

import Definitions.Def_RequestProject_Components
import Definitions.Def_RequestProject_PhiFormula
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial ℕ ℚ) (i : ℕ) :
    pderiv i (∏ x ∈ s, f x) = ∑ x ∈ s, (∏ y ∈ s.erase x, f y) * pderiv i (f x) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, Derivation.leibniz, ih, sum_insert ha, erase_insert ha]
    simp only [smul_eq_mul]
    rw [mul_sum, add_comm]
    congr 1
    refine sum_congr rfl fun x hx => ?_
    have hxa : x ≠ a := fun h => ha (h ▸ hx)
    rw [erase_insert_of_ne hxa.symm, prod_insert (fun h => ha (mem_of_mem_erase h))]
    ring
end ChromaticReconstruction
