-- Prove2me | solution 1 for Finset.affineDim_union_le_sum_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:08:33.448136+00:00
-- url     : https://prove2.me/submissions/c847b016-18e9-405c-8ad9-83f11b252aa7

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDimSumset
public import Theorems.Thm_Finset_affineDim_empty
public import Theorems.Thm_Finset_affineDim_eq_finrank_vectorSpan
public import Theorems.Thm_Finset_affineDim_singleton
public import Theorems.Thm_Finset_affineDim_vadd_finset
attribute [local simp] Finset.affineDim_empty
attribute [local simp] Finset.affineDim_singleton
attribute [local simp] Finset.affineDim_vadd_finset


section
public section
namespace Finset
open scoped Pointwise
variable {D : ℕ}
private lemma vectorSpan_union_le {A B : Finset (Fin D → ℝ)} {a b : Fin D → ℝ} (ha : a ∈ A)
    (hb : b ∈ B) :
    vectorSpan ℝ (↑(A ∪ B) : Set (Fin D → ℝ)) ≤
      vectorSpan ℝ (↑(A + B) : Set (Fin D → ℝ)) ⊔ Submodule.span ℝ {b - a} := by
  rw [vectorSpan_eq_span_vsub_set_right ℝ (p := a) (by simp [ha]), Submodule.span_le]
  rintro v ⟨x, hx, rfl⟩
  simp only [vsub_eq_sub, SetLike.mem_coe]
  obtain hx | hx := mem_union.1 hx
  · apply le_sup_left (b := Submodule.span ℝ {b - a})
    simpa using vsub_mem_vectorSpan ℝ (mem_coe.2 (add_mem_add hx hb))
      (mem_coe.2 (add_mem_add ha hb))
  · rw [← sub_add_sub_cancel x b a]
    apply Submodule.add_mem_sup _ (Submodule.mem_span_singleton_self _)
    simpa using vsub_mem_vectorSpan ℝ (mem_coe.2 (add_mem_add ha hx))
      (mem_coe.2 (add_mem_add ha hb))
end Finset
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Pointwise
variable {D : ℕ}
namespace Finset
theorem _root_.solution {A B : Finset (Fin D → ℝ)}
    (hA : A.Nonempty) (hB : B.Nonempty) :
    (A ∪ B).affineDim ≤ (A + B).affineDim + 1 := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  rw [affineDim_eq_finrank_vectorSpan, affineDim_eq_finrank_vectorSpan]
  apply (Submodule.finrank_mono (vectorSpan_union_le ha hb)).trans
  apply (Submodule.finrank_add_le_finrank_add_finrank _ _).trans
  gcongr
  simpa using finrank_span_le_card ({b - a} : Set (Fin D → ℝ))
end Finset
