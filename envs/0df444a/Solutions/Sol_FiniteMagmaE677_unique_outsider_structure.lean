-- Prove2me | solution 1 for FiniteMagmaE677.unique_outsider_structure
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T08:02:59.834547+00:00
-- url     : https://prove2.me/submissions/2fdfd319-f558-4aa3-b065-669a4511c45d

import Definitions.Def_FiniteMagmaE677
import Theorems.Thm_FiniteMagmaE677_left_bijective
import Theorems.Thm_FiniteMagmaE677_fixer_unique

/-!
# Structural facts about the unique element outside a left orbit

Let `x` be an element of a finite magma satisfying E677, and suppose exactly one
element `A` lies outside the left orbit `O_x = {L_x^n x}`. Then:

1. `A` is `L_x`-fixed: `x ⋄ A = A`. (Surjectivity of `L_x` gives a preimage `B`;
   if `B` were on the orbit then `A = L_x B` would be too, so `B = A` by uniqueness.)
2. The fixer candidate of `A` is `x`: `(A ⋄ A) ⋄ A = x` (fixer uniqueness at `A`).
3. `A` is not idempotent: `A ⋄ A ≠ A` (else `x = (A ⋄ A) ⋄ A = A`, but `x ∈ O_x ≠ A`).
4. `A ⋄ (A ⋄ x) = A` (E677 at `(A, A)` using 2).
5. `A ⋄ x` returns to the orbit: `A ⋄ x ≠ A`, hence `A ⋄ x ∈ O_x`.

No no-fixer hypothesis is needed. This is the opening derivations of the accepted
reduction `unique_left_orbit_complement_collision_gives_fixer` (sketch 139884f7),
made importable.
-/

universe u

theorem FiniteMagmaE677.unique_outsider_structure {α : Type u} [Fintype α]
    (op : α → α → α) (h : FiniteMagmaE677.E677 op) (x A : α)
    (hA_notin : ¬ FiniteMagmaE677.InLeftOrbit op x A)
    (hA_unique : ∀ a : α, ¬ FiniteMagmaE677.InLeftOrbit op x a → a = A) :
    op x A = A ∧
    op (op A A) A = x ∧
    op A A ≠ A ∧
    op A (op A x) = A ∧
    FiniteMagmaE677.InLeftOrbit op x (op A x) ∧
    x ≠ A := by
  have hx_orbit : FiniteMagmaE677.InLeftOrbit op x x := ⟨0, rfl⟩
  -- fact 1: the outsider is L_x-fixed
  have hxA : op x A = A := by
    obtain ⟨B, hB⟩ := (FiniteMagmaE677.left_bijective op h x).2 A
    have hB_notin : ¬ FiniteMagmaE677.InLeftOrbit op x B := by
      rintro ⟨k, hk⟩
      refine hA_notin ⟨k + 1, ?_⟩
      rw [Function.iterate_succ_apply']
      exact hB.symm.trans (congrArg (op x) hk)
    have hBA : B = A := hA_unique B hB_notin
    rw [hBA] at hB
    exact hB
  -- fact 2: fixer candidate of A is x
  have hPhi : op (op A A) A = x :=
    (FiniteMagmaE677.fixer_unique op h A x hxA).symm
  -- fact 3: A not idempotent
  have hAAne : op A A ≠ A := by
    intro hAA
    have hgoal : op (op A A) A = A := by rw [hAA, hAA]
    have hxa : x = A := hPhi.symm.trans hgoal
    exact hA_notin (hxa ▸ hx_orbit)
  -- fact 4: A ◇ (A ◇ x) = A
  have hA_Ax : op A (op A x) = A := by
    have hE := h A A
    rw [hPhi] at hE
    exact hE.symm
  -- fact 5: A ◇ x ≠ A, hence on the orbit
  have hAxne : op A x ≠ A := by
    intro hAx
    apply hAAne
    calc op A A = op A (op A x) := by rw [hAx]
      _ = A := hA_Ax
  refine ⟨hxA, hPhi, hAAne, hA_Ax, ?_, ?_⟩
  · by_contra hnot
    exact hAxne (hA_unique (op A x) hnot)
  · intro hxa
    exact hA_notin (hxa ▸ hx_orbit)

theorem solution {α : Type u} [Fintype α]
    (op : α → α → α) (h : FiniteMagmaE677.E677 op) (x A : α)
    (hA_notin : ¬ FiniteMagmaE677.InLeftOrbit op x A)
    (hA_unique : ∀ a : α, ¬ FiniteMagmaE677.InLeftOrbit op x a → a = A) :
    op x A = A ∧
    op (op A A) A = x ∧
    op A A ≠ A ∧
    op A (op A x) = A ∧
    FiniteMagmaE677.InLeftOrbit op x (op A x) ∧
    x ≠ A :=
  FiniteMagmaE677.unique_outsider_structure op h x A hA_notin hA_unique
