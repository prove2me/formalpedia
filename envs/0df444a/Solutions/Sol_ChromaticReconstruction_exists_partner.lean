-- Prove2me | solution 1 for ChromaticReconstruction.exists_partner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:42:26.653143+00:00
-- url     : https://prove2.me/submissions/72172563-64a3-43b0-a681-30d731ec85e7

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_RecoverP
import Theorems.Thm_ChromaticReconstruction_coeff_fP_lowerAt
import Theorems.Thm_ChromaticReconstruction_coeff_fP_eq_zero
import Theorems.Thm_ChromaticReconstruction_coeff_lowerAt_pos

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {W W' : Multiset ℕ} (h : fP W = fP W') {a : ℕ} (ha : a ∈ bigWeights W) :
    ∃ a' ∈ bigWeights W', lowerAt W a = lowerAt W' a' ∧
      (a - 1) * W.count a = (a' - 1) * W'.count a' := by
  have hc := coeff_fP_lowerAt ha
  rw [h] at hc
  by_contra hne
  push_neg at hne
  have : coeff (Multiset.toFinsupp (lowerAt W a)) (fP W') = 0 := by
    apply coeff_fP_eq_zero
    intro a' ha' heq
    have hc' := coeff_fP_lowerAt ha'
    rw [heq] at hc'
    rw [hc] at hc'
    exact hne a' ha' heq.symm (by exact_mod_cast hc')
  rw [this] at hc
  exact coeff_lowerAt_pos ha hc.symm
end ChromaticReconstruction
