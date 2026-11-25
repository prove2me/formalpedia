-- Prove2me | solution 1 for ChromaticReconstruction.pair_eq_of_first
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:41:51.860321+00:00
-- url     : https://prove2.me/submissions/3891a63c-1b58-4499-a59f-5bdb44ae1980

import Definitions.Def_RequestProject_RecoverP
import Definitions.Def_RequestProject_Theta
import Theorems.Thm_ChromaticReconstruction_pairMS_mk
import Theorems.Thm_ChromaticReconstruction_pairSum_mk
import Theorems.Thm_ChromaticReconstruction_theta_mk
import Theorems.Thm_ChromaticReconstruction_cons_sub_cancel
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
theorem _root_.solution {W : Multiset ℕ} {a b c d : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hab : {a, b} ≤ W) (hcd : {c, d} ≤ W)
    (h : (c + d - 1) ::ₘ (W - {c, d}) = (a + b - 1) ::ₘ (W - {a, b})) :
    ({c, d} : Multiset ℕ) = {a, b} := by
  have e := cons_sub_cancel hcd hab h
  have hm : a + b - 1 ∈ (c + d - 1) ::ₘ ({a, b} : Multiset ℕ) := by rw [e]; simp
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hm
  have hcd' : c + d - 1 = a + b - 1 := by omega
  rw [hcd', Multiset.cons_inj_right] at e
  exact e.symm
end ChromaticReconstruction
