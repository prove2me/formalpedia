-- Prove2me | solution 1 for Erdos287.no_joint_endpoint_family_in_five_prime_classes
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-27T01:16:34.565258+00:00
-- url     : https://prove2.me/submissions/6d5f1f74-0891-4f7a-8592-30af5ca03351

import Mathlib
import Theorems.Thm_Erdos287_endpoint_extremal_cofactor_layer_hits_joint_replacements

open Finset

set_option autoImplicit false

private abbrev commonMultiple : ℕ := 164249358725037825439200

private theorem jointNumeratorResidue (C : Finset ℕ) (hC : C ⊆ Icc 20 55) (hd : 55 ∈ C)
    (hblock : 22 ∈ C ∨ 44 ∈ C) :
    ((∑ a ∈ C, commonMultiple / a : ℕ) : ZMod 11) ∈
      ({0, 2, 3, 5, 8, 10} : Finset (ZMod 11)) := by
  let S : Finset ℕ := {22, 33, 44, 55}
  let T := S.filter (fun a => a ∈ C)
  have hvanish : ∀ a ∈ Icc 20 55, a ∉ S → ((commonMultiple / a : ℕ) : ZMod 11) = 0 := by
    decide
  have hsum : ∑ a ∈ T, ((commonMultiple / a : ℕ) : ZMod 11) =
      ∑ a ∈ C, ((commonMultiple / a : ℕ) : ZMod 11) :=
    sum_subset (fun _ h => (mem_filter.mp h).2) (fun a ha hx =>
      hvanish a (hC ha) (fun haS => hx (mem_filter.mpr ⟨haS, ha⟩)))
  have htable : ∀ U ∈ S.powerset, 55 ∈ U → 22 ∈ U ∨ 44 ∈ U →
      (∑ a ∈ U, ((commonMultiple / a : ℕ) : ZMod 11)) ∈
        ({0, 2, 3, 5, 8, 10} : Finset (ZMod 11)) := by
    decide
  rw [Nat.cast_sum, ← hsum]
  exact htable T (mem_powerset.mpr (filter_subset _ _))
    (mem_filter.mpr ⟨by decide, hd⟩)
    (hblock.imp (fun h => mem_filter.mpr ⟨by decide, h⟩) (fun h => mem_filter.mpr ⟨by decide, h⟩))

/-- A shared prime-power layer with endpoint cofactors 20 and 55 excludes
prime labels in five nonzero classes modulo 11 above the stated threshold. -/
theorem solution (D : Finset ℕ) (p e : ℕ) (hp : p.Prime) (he : 1 ≤ e)
    (hsize : 171783896431127155981377 < 2 * p)
    (hclass : (p : ZMod 11) ∉ ({0, 2, 3, 5, 8, 10} : Finset (ZMod 11))) :
    let m := 20 * p ^ e
    let M := 55 * p ^ e
    m ∈ D → M ∈ D → D ⊆ Finset.Icc m M →
    (∀ x, m ≤ x → x + 1 ≤ M → x ∈ D ∨ x + 1 ∈ D) →
    (∑ n ∈ D, (1 : ℚ) / n = 1) →
    (∀ (a b : ℕ) (F : Finset ℕ), 1 < a → a ∈ F → b ∈ F →
      F ⊆ Finset.Icc a b → (∀ x, a ≤ x → x + 1 ≤ b → x ∈ F ∨ x + 1 ∈ F) →
      (∑ n ∈ F, (1 : ℚ) / n = 1) → M ≤ b ∧ (b = M → a ≤ m)) → False := by
  classical
  intro m M hmD hMD hD hcover hsum hEnd
  have ht : 0 < p ^ e := pow_pos hp.pos _
  have hm : 1 < m := by dsimp [m]; omega
  have hclears : ∀ a ∈ Icc 20 55, a ∣ commonMultiple := by decide
  let C := (Icc 20 55).filter (fun a => a * p ^ e ∈ D)
  obtain ⟨hc, hd, hdiv, hjoint⟩ :=
    Erdos287.endpoint_extremal_cofactor_layer_hits_joint_replacements D p e 20 55
      commonMultiple 0 hp he (by decide) (by simp) hm hmD hMD hD hcover hsum hEnd hclears
  have hA : ({22, 44} : Finset ℕ) ⊆ Ioo 20 55 := by decide
  have hmass : (∑ a ∈ ({22, 44} : Finset ℕ), (1 : ℚ) / a) = 1 / 20 + 1 / 55 := by
    rw [sum_insert (by simp), sum_singleton]
    norm_num
  obtain ⟨a, ha, hasel⟩ := hjoint _ hA hmass
  have hblock : 22 ∈ C ∨ 44 ∈ C := by
    simp only [mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact Or.inl hasel
    · exact Or.inr hasel
  let N := ∑ a ∈ C, commonMultiple / a
  have hpos : 0 < N := (by decide : 0 < commonMultiple / 20).trans_le
    (single_le_sum (f := fun a => commonMultiple / a) (fun _ _ => Nat.zero_le _) hc)
  have hmax : N < 2 * p := by
    calc
      N ≤ ∑ a ∈ Icc 20 55, commonMultiple / a := sum_le_sum_of_subset (filter_subset _ _)
      _ = 171783896431127155981377 := by decide
      _ < 2 * p := hsize
  obtain ⟨k, hk⟩ : p ∣ N := by simpa using hdiv
  have h₁ : 0 < k := (Nat.mul_lt_mul_left hp.pos).mp (by simpa only [mul_zero, ← hk] using hpos)
  have h₂ : k < 2 := (Nat.mul_lt_mul_left hp.pos).mp (by simpa only [← hk, Nat.mul_comm p 2] using hmax)
  have hexact : N = p := by rw [hk, show k = 1 by omega, mul_one]
  have hresidue := jointNumeratorResidue C (filter_subset _ _) hd hblock
  change (N : ZMod 11) ∈ _ at hresidue
  exact hclass (hexact ▸ hresidue)

