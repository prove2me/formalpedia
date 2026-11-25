-- Prove2me | solution 1 for ChromaticReconstruction.coeff_thetaAB_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:48:26.078275+00:00
-- url     : https://prove2.me/submissions/4f9af086-5c21-4254-a100-04c328db0d58

import Definitions.Def_RequestProject_RecoverP
import Definitions.Def_RequestProject_Theta
import Theorems.Thm_ChromaticReconstruction_pairMS_mk
import Theorems.Thm_ChromaticReconstruction_pairSum_mk
import Theorems.Thm_ChromaticReconstruction_theta_mk
import Theorems.Thm_ChromaticReconstruction_pair_eq_of_first
import Theorems.Thm_ChromaticReconstruction_pair_eq_of_second
import Theorems.Thm_ChromaticReconstruction_sym2_eq_of_pair
import Theorems.Thm_ChromaticReconstruction_pair_le_two
import Theorems.Thm_ChromaticReconstruction_coeff_thetaAB
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
theorem _root_.solution {W : Multiset ℕ} (hW : ∀ x ∈ W, 2 ≤ x) {a b c d : ℕ}
    (hab : {a, b} ≤ W) (hcd : {c, d} ≤ W) (hne : s(c, d) ≠ s(a, b)) (hle : a + b ≤ c + d) :
    coeff (Multiset.toFinsupp ((a + b - 1) ::ₘ (W - {a, b}))) (thetaAB W c d) = 0 := by
  obtain ⟨ha, hb⟩ := pair_le_two hW hab
  obtain ⟨hc, hd⟩ := pair_le_two hW hcd
  rw [coeff_thetaAB, if_neg, zero_add]
  · apply sum_eq_zero
    intro r hr
    rw [if_neg]
    intro h
    have hr' : r ∈ W - {c, d} := by
      simp only [bigWeights, mem_filter, Multiset.mem_toFinset] at hr; exact hr.1
    rcases pair_eq_of_second ha hb hc hd hab hcd hr' h with h1 | ⟨h1, _⟩
    · omega
    · exact hne (sym2_eq_of_pair h1)
  · intro h
    exact hne (sym2_eq_of_pair (pair_eq_of_first ha hb hab hcd h))
end ChromaticReconstruction
