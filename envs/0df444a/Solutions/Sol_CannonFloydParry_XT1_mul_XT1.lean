-- Prove2me | solution 1 for CannonFloydParry.XT1_mul_XT1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-25T20:09:18.003989+00:00
-- url     : https://prove2.me/submissions/0f038d06-9ec0-45ac-ae3c-a5b1734373e3

import Definitions.Def_CannonFloydParry_T
import Definitions.Def_CannonFloydParry_Presentations
import Theorems.Thm_CannonFloydParry_Y_conj_eq_Y_succ
import Mathlib

/-! The algebra of `T₁` (CFP pp. 236–238): relations, the map `F₁ → T₁`, `XₙXₖ = XₖXₙ₊₁`,
Lemma 5.5 and Lemma 5.6. -/

namespace CannonFloydParry.S5

open PresentedGroup

local notation "a" => (PresentedGroup.of FormalABC.A : T1)
local notation "b" => (PresentedGroup.of FormalABC.B : T1)
local notation "c" => (PresentedGroup.of FormalABC.C : T1)

lemma mem_rels {r : FreeGroup FormalABC} (h : r ∈ relsT1) : (PresentedGroup.mk relsT1 r) = 1 :=
  PresentedGroup.one_of_mem h

lemma rel1 : (a * b⁻¹) * (a⁻¹ * b * a) * (a * b⁻¹)⁻¹ * (a⁻¹ * b * a)⁻¹ = 1 := by
  have h := mem_rels (r := _) (Or.inl rfl)
  simp only [map_mul, map_inv] at h
  exact h

lemma rel2 : (a * b⁻¹) * (a⁻¹ ^ 2 * b * a ^ 2) * (a * b⁻¹)⁻¹ * (a⁻¹ ^ 2 * b * a ^ 2)⁻¹ = 1 := by
  have h := mem_rels (r := _) (Or.inr (Or.inl rfl))
  simp only [map_mul, map_inv, map_pow] at h
  exact h

/-- The map `F₁ → T₁`, `A ↦ A`, `B ↦ B`. -/
noncomputable def fromF1 : F1 →* T1 :=
  PresentedGroup.toGroup (f := fun s => match s with | FormalAB.A => a | FormalAB.B => b) (by
    intro r hr
    rcases hr with rfl | rfl
    · simpa using rel1
    · simpa using rel2)

@[simp] lemma fromF1_A : fromF1 (PresentedGroup.of FormalAB.A) = a := PresentedGroup.toGroup.of _
@[simp] lemma fromF1_B : fromF1 (PresentedGroup.of FormalAB.B) = b := PresentedGroup.toGroup.of _

lemma fromF1_Y (n : ℕ) : fromF1 (Y n) = XT1 n := by
  cases n <;> simp [Y, XT1, map_mul, map_inv, map_pow]

/-- p. 236: `XₙXₖ = XₖXₙ₊₁` for `k < n`. -/
theorem XT1_mul_XT1' (k n : ℕ) (hkn : k < n) : XT1 n * XT1 k = XT1 k * XT1 (n + 1) := by
  have h := congrArg fromF1 (Y_conj_eq_Y_succ k n hkn)
  simp only [map_mul, map_inv, fromF1_Y] at h
  rw [← h]; group


section Lemma56
variable (n : ℕ) (hn : 0 < n)
include hn

end Lemma56

end CannonFloydParry.S5

open CannonFloydParry

theorem solution (k n : ℕ) (hkn : k < n) : XT1 n * XT1 k = XT1 k * XT1 (n + 1) :=
  CannonFloydParry.S5.XT1_mul_XT1' k n hkn
