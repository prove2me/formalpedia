-- Prove2me | solution 1 for ChromaticReconstruction.fP_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:55:33.076016+00:00
-- url     : https://prove2.me/submissions/d321d08e-6103-49c7-9fe2-47b1588f31d4

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_RecoverP
import Theorems.Thm_ChromaticReconstruction_lowerAt_add
import Theorems.Thm_ChromaticReconstruction_exists_partner
import Theorems.Thm_ChromaticReconstruction_psum_partner
import Theorems.Thm_ChromaticReconstruction_bigWeights_subsingleton
import Theorems.Thm_ChromaticReconstruction_eq_replicate_two
import Theorems.Thm_ChromaticReconstruction_psum_one_of_two_big
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one



set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {W W' : Multiset ℕ} (hW : ∀ x ∈ W, 2 ≤ x) (hW' : ∀ x ∈ W', 2 ≤ x)
    (hcard : Multiset.card W = Multiset.card W') (h : fP W = fP W') : W = W' := by
  by_cases hb : bigWeights W = ∅
  · have hb' : bigWeights W' = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro a' ha'
      obtain ⟨a, ha, _⟩ := exists_partner h.symm ha'
      simp [hb] at ha
    rw [eq_replicate_two hW hb, eq_replicate_two hW' hb', hcard]
  by_contra hne
  obtain ⟨a, ha⟩ := nonempty_iff_ne_empty.2 hb
  have hsub := bigWeights_subsingleton hne h
  have hbA : bigWeights W = {a} := by
    ext x; simp only [mem_singleton]
    exact ⟨fun hx => hsub x hx a ha, fun hx => hx ▸ ha⟩
  obtain ⟨a', ha', hl, hc⟩ := exists_partner h ha
  have hsub' := bigWeights_subsingleton (Ne.symm hne) h.symm
  have hbA' : bigWeights W' = {a'} := by
    ext x; simp only [mem_singleton]
    exact ⟨fun hx => hsub' x hx a' ha', fun hx => hx ▸ ha'⟩
  have haW : a ∈ W ∧ 3 ≤ a := by simpa [bigWeights] using ha
  have haW' : a' ∈ W' ∧ 3 ≤ a' := by simpa [bigWeights] using ha'
  have hp := psum_partner haW.1 haW'.1 (by omega) (by omega) hl 1
  rw [psum_one_of_two_big hW hbA, psum_one_of_two_big hW' hbA', hcard] at hp
  have hc' : ((a : ℤ) - 1) * W.count a = ((a' : ℤ) - 1) * W'.count a' := by
    have := congrArg (fun n : ℕ => (n : ℤ)) hc
    push_cast [Nat.cast_sub (by omega : 1 ≤ a), Nat.cast_sub (by omega : 1 ≤ a')] at this
    linarith
  have hcnt : (W.count a : ℤ) = W'.count a' := by nlinarith
  have hpos : (0 : ℤ) < W.count a := by exact_mod_cast Multiset.count_pos.2 haW.1
  have haa : (a : ℤ) = a' := by
    rw [hcnt] at hc'
    have : (0 : ℤ) < W'.count a' := hcnt ▸ hpos
    nlinarith
  have haa' : a = a' := by exact_mod_cast haa
  subst haa'
  apply hne
  have e1 := lowerAt_add haW.1
  have e2 := lowerAt_add haW'.1
  rw [hl, e2] at e1
  exact (add_right_cancel e1).symm
end ChromaticReconstruction
