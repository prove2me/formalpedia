-- Prove2me | solution 1 for ChromaticReconstruction.sym2_eq_of_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:42:32.261782+00:00
-- url     : https://prove2.me/submissions/0d2d0474-97e4-4c03-a263-021509af4099

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
theorem _root_.solution {a b c d : ℕ} (h : ({c, d} : Multiset ℕ) = {a, b}) :
    s(c, d) = s(a, b) := by
  have h1 := congrArg (Multiset.count c) h
  have h2 := congrArg (Multiset.count d) h
  have h3 := congrArg (Multiset.count a) h
  simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton] at h1 h2 h3
  rw [Sym2.eq_iff]
  split_ifs at h1 h2 h3 <;> omega
end ChromaticReconstruction
