-- Prove2me | solution 1 for ChromaticReconstruction.bigWeights_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:48:00.128446+00:00
-- url     : https://prove2.me/submissions/c6d1c369-00a7-4c83-9e01-93a70a31acb0

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_RecoverP
import Theorems.Thm_ChromaticReconstruction_lowerAt_add
import Theorems.Thm_ChromaticReconstruction_exists_partner
import Theorems.Thm_ChromaticReconstruction_psum_partner
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one



set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {W W' : Multiset ℕ} (hne : W ≠ W') (h : fP W = fP W') : ∀ a ∈ bigWeights W, ∀ b ∈ bigWeights W, a = b := by
  have hW' : ∀ x ∈ bigWeights W, x ∈ W ∧ 3 ≤ x := by
    intro x hx; simpa [bigWeights] using hx
  have key : ∀ a ∈ bigWeights W, ∃ a' : ℕ, 1 ≤ a' ∧ a ≠ a' ∧ ∀ j,
      psum j W - psum j W' =
        ((a' : ℤ) - 1) ^ j + (a : ℤ) ^ j - ((a : ℤ) - 1) ^ j - (a' : ℤ) ^ j := by
    intro a ha
    obtain ⟨a', ha', hl, _⟩ := exists_partner h ha
    have ha'' : a' ∈ W' ∧ 3 ≤ a' := by simpa [bigWeights] using ha'
    refine ⟨a', by omega, ?_, psum_partner (hW' a ha).1 ha''.1 (by linarith [(hW' a ha).2])
      (by omega) hl⟩
    rintro rfl
    apply hne
    have e1 := lowerAt_add (hW' a ha).1
    have e2 := lowerAt_add ha''.1
    rw [hl, e2] at e1
    exact (add_right_cancel e1).symm
  intro a ha b hb
  obtain ⟨a', h1a, hna, hpa⟩ := key a ha
  obtain ⟨b', h1b, hnb, hpb⟩ := key b hb
  have e2 := (hpa 2).symm.trans (hpb 2)
  have e3 := (hpa 3).symm.trans (hpb 3)
  have hA : (a : ℤ) - a' ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hna)
  have e2' : (a : ℤ) - a' = b - b' := by nlinarith
  have e3' : ((a : ℤ) - a') * (a + a' - 1) = ((b : ℤ) - b') * (b + b' - 1) := by nlinarith
  rw [← e2'] at e3'
  have := mul_left_cancel₀ hA e3'
  have : (a : ℤ) = b := by linarith
  exact_mod_cast this
end ChromaticReconstruction
