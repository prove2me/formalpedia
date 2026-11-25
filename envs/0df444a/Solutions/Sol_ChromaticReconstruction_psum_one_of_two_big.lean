-- Prove2me | solution 1 for ChromaticReconstruction.psum_one_of_two_big
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:41:07.644812+00:00
-- url     : https://prove2.me/submissions/b4b575cb-9b73-4092-ae66-0b06813f75f2

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_RecoverP
import Theorems.Thm_ChromaticReconstruction_eq_two_of_not_big
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one



set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {W : Multiset ℕ} (hW : ∀ x ∈ W, 2 ≤ x) {a : ℕ}
    (hb : bigWeights W = {a}) :
    psum 1 W = 2 * ((Multiset.card W : ℤ) - W.count a) + a * W.count a := by
  have hsplit := Multiset.filter_add_not (fun x => x = a) W
  rw [Multiset.filter_eq'] at hsplit
  have hrest : Multiset.filter (fun x => ¬ x = a) W =
      Multiset.replicate (Multiset.card W - W.count a) 2 := by
    rw [Multiset.eq_replicate]
    constructor
    · have := congrArg Multiset.card hsplit
      simp only [Multiset.card_add, Multiset.card_replicate] at this
      omega
    · intro x hx
      rw [Multiset.mem_filter] at hx
      exact eq_two_of_not_big hW hx.1 (by rw [hb]; simpa using hx.2)
  rw [hrest] at hsplit
  conv_lhs => rw [← hsplit]
  simp only [psum, Multiset.map_add, Multiset.map_replicate, Multiset.sum_add,
    Multiset.sum_replicate, pow_one, nsmul_eq_mul]
  have : W.count a ≤ Multiset.card W := Multiset.count_le_card a W
  push_cast [Nat.cast_sub this]
  ring
end ChromaticReconstruction
