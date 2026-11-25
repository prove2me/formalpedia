-- Prove2me | solution 1 for ChromaticReconstruction.prod_X_multiset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:37:46.719051+00:00
-- url     : https://prove2.me/submissions/b7513290-fa54-4dc0-bfc8-1bb23763364a

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_CompStructure
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one



set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution (μ : Multiset ℕ) :
    (μ.map (fun r => (X r : MvPolynomial ℕ ℚ))).prod = monomial (Multiset.toFinsupp μ) 1 := by
  induction μ using Multiset.induction_on with
  | empty => simp
  | cons a μ ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih, ← Multiset.singleton_add,
      Multiset.toFinsupp_add, Multiset.toFinsupp_singleton, X, monomial_mul, one_mul]
end ChromaticReconstruction
