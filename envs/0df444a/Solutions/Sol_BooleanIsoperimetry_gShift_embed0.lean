-- Prove2me | solution 1 for BooleanIsoperimetry.gShift_embed0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:41:19.774818+00:00
-- url     : https://prove2.me/submissions/215290c8-6cc5-46df-8b70-314838433257

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
    gShift (embed0 v) = embed0 (gShift v) := by
  unfold gShift
  by_cases h : v.Nonempty
  · have h0 : (embed0 v).Nonempty := by unfold embed0; simp [h]
    simp only [h, h0, dif_pos]
    have hmin : (embed0 v).min' h0 = Fin.castSucc (v.min' h) := by
      apply le_antisymm
      · apply Finset.min'_le
        unfold embed0
        exact Finset.mem_image_of_mem _ (Finset.min'_mem _ _)
      · apply Finset.le_min'
        intro y hy
        unfold embed0 at hy
        rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
        have : v.min' h ≤ x := Finset.min'_le _ _ hx
        exact Fin.castSucc_le_castSucc_iff.mpr this
    have herase : (embed0 v).erase (Fin.castSucc (v.min' h)) = embed0 (v.erase (v.min' h)) := by
      unfold embed0
      ext x
      simp only [Finset.mem_erase, Finset.mem_image]
      constructor
      · rintro ⟨h1, ⟨y, hy, rfl⟩⟩
        use y
        refine ⟨?_, rfl⟩
        refine ⟨?_, hy⟩
        intro heq
        subst heq
        exact h1 rfl
      · rintro ⟨y, hy, rfl⟩
        refine ⟨?_, ⟨y, hy.2, rfl⟩⟩
        intro heq
        exact hy.1 (Fin.castSucc_inj.mp heq)
    rw [hmin, herase]
  · simp_all [embed0]
end BooleanIsoperimetry
