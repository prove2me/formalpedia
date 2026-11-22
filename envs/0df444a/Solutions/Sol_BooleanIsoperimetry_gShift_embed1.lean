-- Prove2me | solution 1 for BooleanIsoperimetry.gShift_embed1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:41:20.308572+00:00
-- url     : https://prove2.me/submissions/bb229a4d-12ca-445d-89d2-ab6ab1e505ca

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n : ℕ} (v : Cube n) :
    gShift (embed1 v) = if v.Nonempty then embed1 (gShift v) else embed0 ∅ := by
  by_cases h : v.Nonempty
  · have h1 : (embed1 v).Nonempty := by
      unfold embed1
      exact Finset.insert_nonempty _ _
    unfold gShift
    simp only [h, h1, dif_pos, if_pos]
    have hmin : (embed1 v).min' h1 = Fin.castSucc (v.min' h) := by
      apply le_antisymm
      · apply Finset.min'_le
        unfold embed1
        exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.min'_mem _ _))
      · apply Finset.le_min'
        intro y hy
        unfold embed1 at hy
        rcases Finset.mem_insert.mp hy with (rfl | hy)
        · exact le_of_lt (Fin.castSucc_lt_last _)
        · rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
          have : v.min' h ≤ x := Finset.min'_le _ _ hx
          exact Fin.castSucc_le_castSucc_iff.mpr this
    have herase : (embed1 v).erase (Fin.castSucc (v.min' h)) = embed1 (v.erase (v.min' h)) := by
      unfold embed1
      ext x
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_image]
      constructor
      · rintro ⟨h1, (rfl | ⟨y, hy, rfl⟩)⟩
        · exact Or.inl rfl
        · right
          use y
          refine ⟨⟨?_, hy⟩, rfl⟩
          intro heq
          subst heq
          exact h1 rfl
      · rintro (rfl | ⟨y, hy, rfl⟩)
        · refine ⟨?_, Or.inl rfl⟩
          intro heq
          have : (Fin.castSucc (v.min' h) : ℕ) < (Fin.last n : ℕ) := by
            have := Fin.castSucc_lt_last (v.min' h)
            exact this
          have heq_nat : (Fin.castSucc (v.min' h) : ℕ) = (Fin.last n : ℕ) := by rw [heq]
          linarith
        · refine ⟨?_, Or.inr ⟨y, hy.2, rfl⟩⟩
          intro heq
          exact hy.1 (Fin.castSucc_inj.mp heq)
    rw [hmin, herase]
  · simp_all [embed1, embed0, gShift]
end BooleanIsoperimetry
