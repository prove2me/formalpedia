-- Prove2me | solution 1 for ChromaticReconstruction.pair_eq_of_second
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:42:14.608198+00:00
-- url     : https://prove2.me/submissions/6a72f8f0-d188-42d7-8b48-c79fad85ad6b

import Definitions.Def_RequestProject_RecoverP
import Definitions.Def_RequestProject_Theta
import Theorems.Thm_ChromaticReconstruction_pairMS_mk
import Theorems.Thm_ChromaticReconstruction_pairSum_mk
import Theorems.Thm_ChromaticReconstruction_theta_mk
import Theorems.Thm_ChromaticReconstruction_add_sub_cancel_gen
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
theorem _root_.solution {W : Multiset ℕ} {a b c d r : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hc : 2 ≤ c) (hd : 2 ≤ d)
    (hab : {a, b} ≤ W) (hcd : {c, d} ≤ W) (hrW : r ∈ W - {c, d})
    (h : (c + d) ::ₘ lowerAt (W - {c, d}) r = (a + b - 1) ::ₘ (W - {a, b})) :
    c + d + 1 = a + b ∨ (({c, d} : Multiset ℕ) = {a, b} ∧ r = c + d) := by
  have hle : {c, d} + {r} ≤ W := by
    rw [← le_tsub_iff_left hcd]
    simpa using hrW
  have h' : ({c + d, r - 1} : Multiset ℕ) + (W - ({c, d} + {r})) =
      {a + b - 1} + (W - {a, b}) := by
    rw [← tsub_tsub, Multiset.sub_singleton]
    simpa [lowerAt] using h
  have e := add_sub_cancel_gen hle hab h'
  have hm : c + d ∈ ({a + b - 1} : Multiset ℕ) + ({c, d} + {r}) := by
    rw [← e]; simp
  simp only [Multiset.singleton_add, Multiset.insert_eq_cons, Multiset.mem_cons,
    Multiset.mem_add, Multiset.mem_singleton] at hm
  rcases hm with hm | hm | hm
  · left; omega
  · omega
  · right
    subst hm
    have e2 : (c + d - 1) ::ₘ ({a, b} : Multiset ℕ) = (a + b - 1) ::ₘ ({c, d} : Multiset ℕ) := by
      ext x
      have := congrArg (Multiset.count x) e
      simp only [Multiset.insert_eq_cons, Multiset.singleton_add, Multiset.cons_add,
        Multiset.count_cons, Multiset.count_singleton] at this ⊢
      split_ifs at this ⊢ <;> omega
    have hm2 : a + b - 1 ∈ (c + d - 1) ::ₘ ({a, b} : Multiset ℕ) := by rw [e2]; simp
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hm2
    have hr' : c + d - 1 = a + b - 1 := by omega
    rw [hr', Multiset.cons_inj_right] at e2
    exact ⟨e2.symm, rfl⟩
end ChromaticReconstruction
