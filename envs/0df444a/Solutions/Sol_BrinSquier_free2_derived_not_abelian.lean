-- Prove2me | solution 1 for BrinSquier.free2_derived_not_abelian
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-13T07:04:32.945781+00:00
-- url     : https://prove2.me/submissions/e5d0d5f3-1e75-41a4-a08f-4fe3bde3a63b

import Mathlib

open scoped commutatorElement

theorem solution :
    ∃ u v : FreeGroup (Fin 2), u ∈ commutator (FreeGroup (Fin 2)) ∧
      v ∈ commutator (FreeGroup (Fin 2)) ∧ u * v ≠ v * u := by
  refine ⟨⁅FreeGroup.of (0 : Fin 2), FreeGroup.of (1 : Fin 2)⁆,
    ⁅FreeGroup.of (0 : Fin 2), FreeGroup.of (1 : Fin 2) ^ 2⁆,
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _),
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _), ?_⟩
  intro key
  set x : Equiv.Perm (Fin 4) := Equiv.swap 2 3 with hx
  set y : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2 with hy
  set φ : FreeGroup (Fin 2) →* Equiv.Perm (Fin 4) :=
    FreeGroup.lift (fun i : Fin 2 => if i = 0 then x else y) with hφ
  have h1 : φ (FreeGroup.of (0 : Fin 2)) = x := by simp [hφ]
  have h2 : φ (FreeGroup.of (1 : Fin 2)) = y := by simp [hφ]
  have hbad := congrArg φ key
  simp only [commutatorElement_def, map_mul, map_inv, map_pow, h1, h2] at hbad
  rw [hx, hy] at hbad
  revert hbad
  decide
