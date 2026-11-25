-- Prove2me | solution 1 for ChromaticReconstruction.killP1_prod_eq_zero_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:12:10.556362+00:00
-- url     : https://prove2.me/submissions/7c5c9715-4db4-433b-b7e2-92b469d3a17a

import Definitions.Def_RequestProject_Components
import Definitions.Def_RequestProject_PhiFormula
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
omit [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution {P : Finset (Finset V)} {u : V} (hu : {u} ∈ P) :
    killP1 (∏ D ∈ P, X D.card) = 0 := by
  rw [← mul_prod_erase P _ hu, map_mul]
  simp
end ChromaticReconstruction
