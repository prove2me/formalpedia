-- Prove2me | solution 1 for Formalism.CyclotomicNorms.residueMatrixData.exists_dvd_all_of_total
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:57.340793+00:00
-- url     : https://prove2.me/submissions/191d8ec2-c5f2-4386-a8a7-0e9222222f5c

import Definitions.Def_Formalism_CyclotomicNorms_StatementTW
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_ResModule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open Formalism Formalism.CyclotomicNorms
noncomputable section
open Formalism.CyclotomicNorms.residueMatrixData
variable {R : Type*} [CommRing R]
namespace Formalism.CyclotomicNorms.residueMatrixData
theorem _root_.solution (hR : ∀ x y : R, x ∣ y ∨ y ∣ x) {ι : Type*} (s : Finset ι)
    (hs : s.Nonempty) (f : ι → R) : ∃ i ∈ s, ∀ j ∈ s, f i ∣ f j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | insert a s ha ih =>
    rcases s.eq_empty_or_nonempty with h | h
    · exact ⟨a, by simp, by simp [h]⟩
    obtain ⟨i, hi, hij⟩ := ih h
    rcases hR (f a) (f i) with h' | h'
    · refine ⟨a, by simp, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact dvd_refl _
      · exact h'.trans (hij j hj)
    · refine ⟨i, by simp [hi], ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact h'
      · exact hij j hj
end Formalism.CyclotomicNorms.residueMatrixData
