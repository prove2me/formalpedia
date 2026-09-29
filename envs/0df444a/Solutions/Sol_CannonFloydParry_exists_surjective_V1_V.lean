-- Prove2me | solution 1 for CannonFloydParry.exists_surjective_V1_V
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-26T11:51:18.390981+00:00
-- url     : https://prove2.me/submissions/6abb90bb-e577-4841-87b6-144579ae70be

import Definitions.Def_CannonFloydParry_V
import Theorems.Thm_CannonFloydParry_closure_range_symV_eq_V_and_relations
import Mathlib

/-! `V₁ → V` is onto (CFP p. 242–243): by Lemma 6.1 the generators `A, B, C, π₀` of `V`
satisfy the fourteen relations of `V₁` and generate `V`. -/

namespace CannonFloydParry.SurjV1V

open Equiv

/-- Every relator of `V₁` maps to `1` under `A, B, C, π₀ ↦ symV`. -/
lemma rels_lift (r : FreeGroup FormalV) (hr : r ∈ relsV1) : FreeGroup.lift symV r = 1 := by
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ :=
    closure_range_symV_eq_V_and_relations
  simp only [relsV1, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [XV] using h1
  · simpa [XV] using h2
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [← CV, ← CV, h3]; group
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [← CV, ← CV, ← XV, h4]; group
  · simp only [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of]
    rw [← CV, ← CV, h5]; group
  · simpa [CV] using h6
  · simpa [piV] using h7
  · simp only [map_mul, map_inv]
    rw [← piV, ← piV, h8]; group
  · simpa [piV] using h9
  · simp only [map_mul, map_inv]
    rw [← piV, ← XV, h10]; group
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [← piV, ← piV, ← XV, h11]; group
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [← piV, ← piV, h12]; group
  · simp only [map_mul, map_inv]
    rw [← piV, ← piV, ← CV, h13]; group
  · simpa [piV, CV] using h14

/-- The homomorphism `V₁ → Perm S¹` sending each generator to its map. -/
noncomputable def toCirc : V1 →* Perm UnitAddCircle := PresentedGroup.toGroup rels_lift

lemma toCirc_range : toCirc.range = Subgroup.closure (Set.range symV) := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
    ← Set.range_comp]
  congr 1

end CannonFloydParry.SurjV1V

open CannonFloydParry in
theorem solution :
    ∃ φ : V1 →* V, Function.Surjective φ ∧
      ∀ s, (φ (PresentedGroup.of s) : Equiv.Perm UnitAddCircle) = symV s := by
  have hcl := closure_range_symV_eq_V_and_relations.1
  have hmem : ∀ g, SurjV1V.toCirc g ∈ V := fun g => hcl ▸ SurjV1V.toCirc_range ▸ ⟨g, rfl⟩
  refine ⟨SurjV1V.toCirc.codRestrict V hmem, ?_, fun s => PresentedGroup.toGroup.of SurjV1V.rels_lift⟩
  rintro ⟨f, hf⟩
  rw [← hcl, ← SurjV1V.toCirc_range] at hf
  obtain ⟨g, rfl⟩ := hf
  exact ⟨g, rfl⟩
