-- Prove2me | solution 1 for BurauFaithful.burau_faithful_three
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-29T01:41:41.611977+00:00
-- url     : https://prove2.me/submissions/de4fa725-1233-4990-80cb-35c9930d047f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_BurauFaithful_UnreducedBurau
import Theorems.Thm_BurauFaithful_burau_three_kernel_word_criterion

set_option autoImplicit false

namespace BurauFaithful

open BraidsLinksMCG

/-- On two generators there is no commuting relation: the only pair of indices has distance `1`. -/
lemma braidRels_three_eq_singleton :
    braidRels 3 = {r | ∃ i j : Fin 2, (j : ℕ) = (i : ℕ) + 1 ∧
      r = FreeGroup.of i * FreeGroup.of j * FreeGroup.of i *
            (FreeGroup.of j * FreeGroup.of i * FreeGroup.of j)⁻¹} := by
  ext r
  simp only [braidRels, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (⟨i, j, h, rfl⟩ | h)
    · exfalso
      have hi : (i : ℕ) < 2 := i.isLt
      have hj : (j : ℕ) < 2 := j.isLt
      omega
    · exact h
  · exact Or.inr

lemma braidRels_three_subset :
    braidRels 3 ⊆ ({braidRel3} : Set (FreeGroup (Fin 2))) := by
  intro r hr
  rw [braidRels_three_eq_singleton] at hr
  obtain ⟨i, j, hij, rfl⟩ := hr
  have hi : (i : ℕ) < 2 := i.isLt
  have hj : (j : ℕ) < 2 := j.isLt
  have hi0 : (i : ℕ) = 0 := by omega
  have hj1 : (j : ℕ) = 1 := by omega
  have hieq : i = (0 : Fin 2) := Fin.ext hi0
  have hjeq : j = (1 : Fin 2) := Fin.ext hj1
  subst hieq; subst hjeq
  simp [braidRel3]

lemma singleton_subset_braidRels_three :
    ({braidRel3} : Set (FreeGroup (Fin 2))) ⊆ braidRels 3 := by
  intro r hr
  rw [Set.mem_singleton_iff] at hr
  subst hr
  rw [braidRels_three_eq_singleton]
  exact ⟨0, 1, rfl, rfl⟩

/-- `B₃` is the presented group `⟨σ₁, σ₂ | σ₁σ₂σ₁ = σ₂σ₁σ₂⟩`: the normal closure of Artin's
relations on three strands is the normal closure of the single braid relation. -/
lemma normalClosure_braidRels_three :
    Subgroup.normalClosure (braidRels 3) =
      Subgroup.normalClosure ({braidRel3} : Set (FreeGroup (Fin 2))) :=
  le_antisymm
    (Subgroup.normalClosure_le_normal fun _ hx =>
      Subgroup.subset_normalClosure (braidRels_three_subset hx))
    (Subgroup.normalClosure_le_normal fun _ hx =>
      Subgroup.subset_normalClosure (singleton_subset_braidRels_three hx))

end BurauFaithful

/-- **Magnus–Peluso (Theorem 4.1):** the unreduced Burau representation `ρ₃` of the three-strand
braid group `B₃` is faithful. -/
theorem solution : Function.Injective (BurauFaithful.burauRep 3) := by
  rw [injective_iff_map_eq_one]
  intro β hβ
  obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective (BraidsLinksMCG.braidRels 3) β
  have hmem := (BurauFaithful.burau_three_kernel_word_criterion w).mp hβ
  rw [← BurauFaithful.normalClosure_braidRels_three] at hmem
  exact PresentedGroup.mk_eq_one_iff.mpr hmem
