-- Prove2me | solution 1 for CompleteOrthogonalIdempotents.exists_forall_mul_eq_mul_pow_val_of_pow_eq_one_of_isUnit_one_sub_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/f2454180-5dfe-58c4-868b-ce366022e8d6

import Mathlib
import Theorems.Thm_exists_completeOrthogonalIdempotents_mul_eq_pow_mul_of_pow_eq_one_of_forall_isUnit_one_sub_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CompleteOrthogonalIdempotents_exists_forall_mul_eq_mul_pow_val_of_pow_eq_one_of_isUnit_one_sub_pow

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace TN
namespace Disc

section COI
variable {R : Type*} [CommRing R]

theorem coi_pi {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (F : ι → κ → R)
    (hF : ∀ i, CompleteOrthogonalIdempotents (F i)) :
    CompleteOrthogonalIdempotents (fun p : ι → κ => ∏ i, F i (p i)) := by
  rw [CompleteOrthogonalIdempotents.iff_ortho_complete]
  constructor
  · intro p q hpq
    obtain ⟨i, hi⟩ : ∃ i, p i ≠ q i := by
      by_contra hc; push Not at hc; exact hpq (funext hc)
    show (∏ i, F i (p i)) * (∏ i, F i (q i)) = 0
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_zero (Finset.mem_univ i) ((hF i).ortho hi)
  · show ∑ p : ι → κ, ∏ i, F i (p i) = 1
    rw [← Fintype.prod_sum]
    exact Finset.prod_eq_one fun i _ => (hF i).complete

theorem pi_mul_apply {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (F : ι → κ → R)
    (hF : ∀ i, CompleteOrthogonalIdempotents (F i)) (p : ι → κ) (i : ι) :
    (∏ i, F i (p i)) * F i (p i) = ∏ i, F i (p i) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_right_comm, (hF i).idem _ |>.eq]

end COI

section Cyc
variable {R : Type*} [CommRing R] {N : ℕ} (ζ : R)

theorem pow_val_eq (hζ : ζ ^ (N + 1) = 1) (m : ℕ) : ζ ^ (m % (N + 1)) = ζ ^ m := by
  conv_rhs => rw [← Nat.mod_add_div m (N + 1), pow_add, pow_mul, hζ, one_pow, mul_one]

theorem pow_val_add (hζ : ζ ^ (N + 1) = 1) (a b : ZMod (N + 1)) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [ZMod.val_add, pow_val_eq ζ hζ, pow_add]

theorem eq_of_pow_val_mul_eq (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (a b : ZMod (N + 1)) (ε : R) (hε : ε ≠ 0) (h : ε * ζ ^ a.val = ε * ζ ^ b.val) : a = b := by
  by_contra hab
  have hva := ZMod.val_lt a
  have hvb := ZMod.val_lt b
  have hne : a.val ≠ b.val := fun hv => hab (ZMod.val_injective _ hv)
  have hζunit : IsUnit ζ := IsUnit.of_pow_eq_one hζ (Nat.succ_ne_zero N)
  have key : ∀ (x y : ℕ), x < y → y < N + 1 → ε * ζ ^ x = ε * ζ ^ y → False := by
    intro x y hxy hy hxy'
    have hu : IsUnit (1 - ζ ^ (y - x)) := hζu _ (Nat.sub_pos_of_lt hxy) (by omega)
    have h0 : ε * (ζ ^ x * (1 - ζ ^ (y - x))) = 0 := by
      rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hxy.le, mul_sub, hxy', sub_self]
    exact hε (((hζunit.pow x).mul hu).mul_left_eq_zero.mp h0)
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact key _ _ hlt hvb h
  · exact key _ _ hgt hva h.symm

end Cyc

end TN.Disc

namespace TN
namespace Disc

theorem main {K : Type*} [AddCommGroup K] [Fintype K] [DecidableEq K] (N : ℕ)
    {R : Type*} [CommRing R] (hd : IsUnit ((N + 1 : ℕ) : R)) (ζ : R) (hζ : ζ ^ (N + 1) = 1)
    (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (e : K → K → Rˣ) (hed : ∀ k k' : K, e k k' ^ (N + 1) = 1)
    (he₁ : ∀ k₁ k₂ k' : K, e (k₁ + k₂) k' = e k₁ k' * e k₂ k') (he₂ : ∀ k k₁ k₂ : K, e k (k₁ + k₂) = e k k₁ * e k k₂)
    (hee : ∀ k : K, e k k = 1) :
    ∃ ε : (K → K → ZMod (N + 1)) → R, CompleteOrthogonalIdempotents ε ∧
      (∀ (B : K → K → ZMod (N + 1)) (k k' : K), ε B * (e k k' : R) = ε B * ζ ^ (B k k').val) ∧
      (∀ B : K → K → ZMod (N + 1), ε B ≠ 0 →
        (∀ k₁ k₂ k' : K, B (k₁ + k₂) k' = B k₁ k' + B k₂ k') ∧ (∀ k k₁ k₂ : K, B k (k₁ + k₂) = B k k₁ + B k k₂) ∧
        (∀ k : K, B k k = 0)) := by
  classical

  have hu : ∀ q : K × K, ((e q.1 q.2 : Rˣ) : R) ^ (N + 1) = 1 := fun q => by
    rw [← Units.val_pow_eq_pow_val, hed, Units.val_one]
  choose f hf hfu using fun q : K × K =>
    exists_completeOrthogonalIdempotents_mul_eq_pow_mul_of_pow_eq_one_of_forall_isUnit_one_sub_pow R N hd ζ hζ hζu _ (hu q)

  let E : (K × K → ZMod (N + 1)) → R := fun p => ∏ q, f q (p q)
  have hE : CompleteOrthogonalIdempotents E := coi_pi f hf
  have hv : ∀ x : ZMod (N + 1), x.val = Fin.val x := fun x => rfl
  have hEe : ∀ (p : K × K → ZMod (N + 1)) (q : K × K), E p * (e q.1 q.2 : R) = E p * ζ ^ (p q).val := by
    intro p q
    rw [hv]
    calc E p * (e q.1 q.2 : R) = (∏ q, f q (p q)) * f q (p q) * (e q.1 q.2 : R) := by rw [pi_mul_apply f hf p q]
      _ = (∏ q, f q (p q)) * ((e q.1 q.2 : R) * f q (p q)) := by ring
      _ = (∏ q, f q (p q)) * (ζ ^ Fin.val (p q) * f q (p q)) := by rw [hfu q (p q)]
      _ = (∏ q, f q (p q)) * f q (p q) * ζ ^ Fin.val (p q) := by ring
      _ = E p * ζ ^ Fin.val (p q) := by rw [pi_mul_apply f hf p q]

  let cur : (K × K → ZMod (N + 1)) ≃ (K → K → ZMod (N + 1)) := Equiv.curry K K (ZMod (N + 1))
  refine ⟨E ∘ cur.symm, (CompleteOrthogonalIdempotents.equiv cur.symm).mpr hE, ?_, ?_⟩
  · intro B k k'
    exact hEe (cur.symm B) (k, k')
  · intro B hB
    have hB' : ∀ k k', (E ∘ cur.symm) B * (e k k' : R) = (E ∘ cur.symm) B * ζ ^ (B k k').val :=
      fun k k' => hEe (cur.symm B) (k, k')
    refine ⟨fun k₁ k₂ k' => ?_, fun k k₁ k₂ => ?_, fun k => ?_⟩
    · apply eq_of_pow_val_mul_eq ζ hζ hζu _ _ _ hB
      rw [← hB', he₁, Units.val_mul, ← mul_assoc, hB', mul_right_comm, hB', pow_val_add ζ hζ]; ring
    · apply eq_of_pow_val_mul_eq ζ hζ hζu _ _ _ hB
      rw [← hB', he₂, Units.val_mul, ← mul_assoc, hB', mul_right_comm, hB', pow_val_add ζ hζ]; ring
    · apply eq_of_pow_val_mul_eq ζ hζ hζu _ _ _ hB
      rw [← hB', hee, Units.val_one, mul_one, ZMod.val_zero, pow_zero, mul_one]

end TN.Disc

theorem solution
    {K : Type*} [AddCommGroup K] [Fintype K] [DecidableEq K] {d : ℕ} [NeZero d]
    {R : Type*} [CommRing R] (hd : IsUnit ((d : ℕ) : R)) (ζ : R) (hζ : ζ ^ d = 1) (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j))
    (e : K → K → Rˣ) (hed : ∀ k k' : K, e k k' ^ d = 1)
    (he₁ : ∀ k₁ k₂ k' : K, e (k₁ + k₂) k' = e k₁ k' * e k₂ k') (he₂ : ∀ k k₁ k₂ : K, e k (k₁ + k₂) = e k k₁ * e k k₂)
    (hee : ∀ k : K, e k k = 1) :
    ∃ ε : (K → K → ZMod d) → R, CompleteOrthogonalIdempotents ε ∧
      (∀ (B : K → K → ZMod d) (k k' : K), ε B * (e k k' : R) = ε B * ζ ^ (B k k').val) ∧
      (∀ B : K → K → ZMod d, ε B ≠ 0 →
        (∀ k₁ k₂ k' : K, B (k₁ + k₂) k' = B k₁ k' + B k₂ k') ∧ (∀ k k₁ k₂ : K, B k (k₁ + k₂) = B k k₁ + B k k₂) ∧
        (∀ k : K, B k k = 0)) := by
  obtain ⟨N, rfl⟩ : ∃ N, d = N + 1 := ⟨d - 1, by have := NeZero.ne d; omega⟩
  exact TN.Disc.main N hd ζ hζ hζu e hed he₁ he₂ hee

end S_CompleteOrthogonalIdempotents_exists_forall_mul_eq_mul_pow_val_of_pow_eq_one_of_isUnit_one_sub_pow
end P2MW
export P2MW.S_CompleteOrthogonalIdempotents_exists_forall_mul_eq_mul_pow_val_of_pow_eq_one_of_isUnit_one_sub_pow (solution)
