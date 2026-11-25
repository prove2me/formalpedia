-- Prove2me | solution 1 for ChromaticReconstruction.phi_leafExt_eq_sum_masterTerm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:48:30.000165+00:00
-- url     : https://prove2.me/submissions/17c86e19-875e-417b-8649-9cf3e6e58719

import Definitions.Def_RequestProject_LeafExtMaster
import Definitions.Def_RequestProject_Theta
import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_Recovery
import Theorems.Thm_ChromaticReconstruction_phi_leafExt


set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K]
variable (S : SimpleGraph K) (m : K → ℕ)
namespace ChromaticReconstruction
theorem _root_.solution (hm : ∀ i, 1 ≤ m i) :
    phi (leafExt S m) = ∑ F ∈ S.edgeFinset.powerset,
      (-1) ^ ((∑ i, m i) - 1 + F.card) * masterTerm m F := by
  rw [phi_leafExt (S := S) hm, sum_comm]
  refine sum_congr rfl fun F _ => ?_
  unfold masterTerm
  rw [mul_sum, Fintype.sum_sigma]
  refine sum_congr rfl fun i _ => ?_
  have hconst : ∑ _ : Fin (m i), ((-1 : MvPolynomial ℕ ℚ) ^ ((∑ j, m j) - 1 + F.card) *
      killP1 (∏ C ∈ compSets (F : Set (Sym2 K)),
        X ((∑ j ∈ C, (m j + 1)) - if i ∈ C then 1 else 0))) =
      (-1) ^ ((∑ j, m j) - 1 + F.card) * ((m i : MvPolynomial ℕ ℚ) *
      killP1 (∏ C ∈ compSets (F : Set (Sym2 K)),
        X ((∑ j ∈ C, (m j + 1)) - if i ∈ C then 1 else 0))) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  exact (Finset.sum_congr rfl fun _ _ => rfl).trans hconst
end ChromaticReconstruction
