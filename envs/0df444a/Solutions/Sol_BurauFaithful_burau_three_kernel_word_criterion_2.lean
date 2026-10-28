-- Prove2me | solution 2 for BurauFaithful.burau_three_kernel_word_criterion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T09:18:32.338731+00:00
-- url     : https://prove2.me/submissions/748f579a-87e4-4e7e-933a-83171918b0e8

import Theorems.Thm_BurauFaithful_burau_faithful_three
import Definitions.Def_BurauFaithful_UnreducedBurau

set_option autoImplicit false

namespace BurauFaithful

/-- The single Artin relation `σ₁σ₂σ₁(σ₂σ₁σ₂)⁻¹` of `B₃`, as a word in the free group on the
generators `σ₁`, `σ₂`. -/
def braidRel3_L213 : FreeGroup (Fin 2) :=
  FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) * FreeGroup.of (0 : Fin 2) *
    (FreeGroup.of (1 : Fin 2) * FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2))⁻¹

end BurauFaithful

namespace BurauFaithful.EZ213

open BraidsLinksMCG
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
    braidRels 3 ⊆ ({braidRel3_L213} : Set (FreeGroup (Fin 2))) := by
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
  simp [braidRel3_L213]

lemma singleton_subset_braidRels_three :
    ({braidRel3_L213} : Set (FreeGroup (Fin 2))) ⊆ braidRels 3 := by
  intro r hr
  rw [Set.mem_singleton_iff] at hr
  subst hr
  rw [braidRels_three_eq_singleton]
  exact ⟨0, 1, rfl, rfl⟩

/-- The normal closure of Artin's relations on three strands is the normal closure of the single braid
relation: `B₃ = ⟨σ₁, σ₂ | σ₁σ₂σ₁ = σ₂σ₁σ₂⟩`. -/
lemma normalClosure_braidRels_three :
    Subgroup.normalClosure (braidRels 3) =
      Subgroup.normalClosure ({braidRel3_L213} : Set (FreeGroup (Fin 2))) :=
  le_antisymm
    (Subgroup.normalClosure_le_normal fun _ hx =>
      Subgroup.subset_normalClosure (braidRels_three_subset hx))
    (Subgroup.normalClosure_le_normal fun _ hx =>
      Subgroup.subset_normalClosure (singleton_subset_braidRels_three hx))

end BurauFaithful.EZ213

theorem solution (w : FreeGroup (Fin 2)) :
    BurauFaithful.burauRep 3 (PresentedGroup.mk (BraidsLinksMCG.braidRels 3) w) = 1 ↔
      w ∈ Subgroup.normalClosure ({BurauFaithful.braidRel3_L213} : Set (FreeGroup (Fin 2))) := by
  rw [← BurauFaithful.EZ213.normalClosure_braidRels_three]
  constructor
  · intro h
    have h1 : (PresentedGroup.mk (BraidsLinksMCG.braidRels 3) w) = 1 :=
      BurauFaithful.burau_faithful_three (h.trans (map_one _).symm)
    exact (QuotientGroup.eq_one_iff w).mp h1
  · intro h
    have h1 : (PresentedGroup.mk (BraidsLinksMCG.braidRels 3) w) = 1 :=
      (QuotientGroup.eq_one_iff w).mpr h
    rw [h1]
    exact map_one _
