-- Prove2me | solution 1 for CannonFloydParry.exists_surjective_T1_T
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-25T20:05:37.345128+00:00
-- url     : https://prove2.me/submissions/2b3e07da-4ee4-44c8-8313-1376f34f60bb

import Theorems.Thm_CannonFloydParry_closure_range_symT_eq_T_and_relations
import Mathlib

/-! Lemma 5.3 from Lemma 5.2; Corollary 5.9 from Lemma 5.3 and Theorem 5.8; the goal. -/

namespace CannonFloydParry.S5

/-- Lemma 5.3. -/
theorem exists_surjective_T1_T' :
    ∃ φ : T1 →* T, Function.Surjective φ ∧
      ∀ s, (φ (PresentedGroup.of s) : Equiv.Perm UnitAddCircle) = symT s := by
  obtain ⟨hcl, hrel⟩ := closure_range_symT_eq_T_and_relations
  dsimp only at hrel
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hrel
  have mem : ∀ s, symT s ∈ T := fun s => hcl ▸ Subgroup.subset_closure ⟨s, rfl⟩
  let f : FormalABC → T := fun s => ⟨symT s, mem s⟩
  have lift_coe : ∀ r, ((FreeGroup.lift f r : T) : Equiv.Perm UnitAddCircle) = FreeGroup.lift symT r := by
    intro r
    have : T.subtype.comp (FreeGroup.lift f) = FreeGroup.lift symT :=
      FreeGroup.ext_hom _ _ (fun s => by simp [f])
    exact DFunLike.congr_fun this r
  have hr : ∀ r ∈ relsT1, FreeGroup.lift f r = 1 := by
    intro r hr
    apply Subtype.ext
    rw [lift_coe]
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, Subgroup.coe_one]
    · exact h1
    · exact h2
    · rw [mul_assoc, inv_mul_eq_one]; exact h3
    · rw [mul_assoc, inv_mul_eq_one]; exact h4
    · rw [inv_mul_eq_one]; exact h5
    · exact h6
  refine ⟨PresentedGroup.toGroup hr, ?_, fun s => by simp [PresentedGroup.toGroup.of, f]⟩
  rw [← MonoidHom.range_eq_top]
  have htop : Subgroup.closure (Set.range f) = ⊤ := by
    apply Subgroup.map_injective T.subtype_injective
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype, ← Set.range_comp]
    exact hcl
  rw [eq_top_iff, ← htop, Subgroup.closure_le]
  rintro _ ⟨s, rfl⟩
  exact ⟨PresentedGroup.of s, PresentedGroup.toGroup.of hr⟩

end CannonFloydParry.S5

open CannonFloydParry

theorem solution :
    ∃ φ : T1 →* T, Function.Surjective φ ∧
      ∀ s, (φ (PresentedGroup.of s) : Equiv.Perm UnitAddCircle) = symT s :=
  CannonFloydParry.S5.exists_surjective_T1_T'
