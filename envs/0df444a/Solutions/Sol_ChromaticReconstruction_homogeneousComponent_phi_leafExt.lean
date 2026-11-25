-- Prove2me | solution 1 for ChromaticReconstruction.homogeneousComponent_phi_leafExt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:03:48.898376+00:00
-- url     : https://prove2.me/submissions/c7ece88a-b20f-46c0-b2f8-61aad468a772

import Definitions.Def_RequestProject_LeafExtMaster
import Definitions.Def_RequestProject_Theta
import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_Recovery
import Theorems.Thm_ChromaticReconstruction_phi_leafExt_eq_sum_masterTerm
import Theorems.Thm_ChromaticReconstruction_masterTerm_isHomogeneous

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K]
variable (S : SimpleGraph K) (m : K → ℕ)
namespace ChromaticReconstruction
theorem _root_.solution (hm : ∀ i, 1 ≤ m i) (j : ℕ) :
    homogeneousComponent j (phi (leafExt S m)) =
      ∑ F ∈ S.edgeFinset.powerset.filter
          (fun F : Finset (Sym2 K) => (compSets (F : Set (Sym2 K))).card = j),
        (-1) ^ ((∑ i, m i) - 1 + F.card) * masterTerm m F := by
  rw [phi_leafExt_eq_sum_masterTerm S m hm, map_sum, sum_filter]
  refine sum_congr rfl fun F _ => ?_
  have hmem : ((-1) ^ ((∑ i, m i) - 1 + F.card) * masterTerm m F : MvPolynomial ℕ ℚ) ∈
      homogeneousSubmodule ℕ ℚ (compSets (F : Set (Sym2 K))).card := by
    have := (isHomogeneous_C ℕ ((-1 : ℚ) ^ ((∑ i, m i) - 1 + F.card))).mul
      (masterTerm_isHomogeneous m F)
    rw [zero_add, map_pow, map_neg, map_one] at this
    exact this
  rw [homogeneousComponent_of_mem hmem]
  by_cases h : (compSets (F : Set (Sym2 K))).card = j
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (Ne.symm h), if_neg h]
end ChromaticReconstruction
