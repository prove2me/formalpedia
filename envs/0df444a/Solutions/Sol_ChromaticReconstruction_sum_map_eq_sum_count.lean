-- Prove2me | solution 1 for ChromaticReconstruction.sum_map_eq_sum_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:47:12.950485+00:00
-- url     : https://prove2.me/submissions/b9edc43c-bb0b-4fcb-932f-ab373e501ae9

import Definitions.Def_RequestProject_RecoverP
import Definitions.Def_RequestProject_Theta
import Theorems.Thm_ChromaticReconstruction_pairMS_mk
import Theorems.Thm_ChromaticReconstruction_pairSum_mk
import Theorems.Thm_ChromaticReconstruction_theta_mk
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one


attribute [local simp] ChromaticReconstruction.pairMS_mk
attribute [local simp] ChromaticReconstruction.pairSum_mk
attribute [local simp] ChromaticReconstruction.theta_mk

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {α M : Type*} [DecidableEq α] [AddCommMonoid M] (E : Multiset α)
    (S : Finset α) (hS : E.toFinset ⊆ S) (f : α → M) :
    (E.map f).sum = ∑ z ∈ S, E.count z • f z := by
  rw [Finset.sum_multiset_map_count]
  apply sum_subset hS
  intro z _ hz
  rw [Multiset.count_eq_zero_of_notMem (by simpa using hz), zero_smul]
end ChromaticReconstruction
