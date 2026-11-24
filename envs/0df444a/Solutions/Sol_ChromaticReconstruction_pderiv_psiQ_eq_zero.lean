-- Prove2me | solution 1 for ChromaticReconstruction.pderiv_psiQ_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T15:09:20.539094+00:00
-- url     : https://prove2.me/submissions/e4ff8fca-d687-4588-8677-f5eb9aed7694

import Definitions.Def_RequestProject_LeafExtMaster
import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_Uniform

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution {q j : ℕ} (hj : ∀ x, q * x ≠ j) (g : MvPolynomial ℕ ℚ) :
    pderiv j (psiQ q g) = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro h
  obtain ⟨i, _, hi⟩ := mem_vars_rename _ g h
  exact hj i hi
end ChromaticReconstruction
