-- Prove2me | solution 1 for ChromaticReconstruction.phi_eq_sum_phiTerm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:16:37.963129+00:00
-- url     : https://prove2.me/submissions/0e9ed516-5bdd-4b5b-993c-4f16b656e49c

import Definitions.Def_RequestProject_Components
import Definitions.Def_RequestProject_PhiFormula
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_killP1_pderiv_typeMonomial
attribute [local simp] ChromaticReconstruction.killP1_X_one

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution (G : SimpleGraph V) :
    phi G = ∑ A ∈ G.edgeFinset.powerset, ∑ v, phiTerm A v := by
  unfold phi chromSymm
  rw [map_sum, map_sum]
  refine sum_congr rfl fun A _ => ?_
  have hc : ((-1 : MvPolynomial ℕ ℚ) ^ A.card) = C ((-1) ^ A.card) := by simp
  rw [hc, pderiv_C_mul, map_mul, killP1_pderiv_typeMonomial, mul_sum]
  refine sum_congr rfl fun v _ => ?_
  unfold phiTerm
  split_ifs <;> simp [killP1]
end ChromaticReconstruction
