-- Prove2me | solution 1 for Erdos338Proof.exists_multiset_of_nsmul_eq_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:59:41.144351+00:00
-- url     : https://prove2.me/submissions/f6edb394-5324-4012-9893-d27c22ef0a1c

module
public import Mathlib
public import Definitions.Def_Erdos338_Kneser_Kneser
public import Definitions.Def_Erdos338_Covering
public import Theorems.Thm_Erdos338Proof_exists_multiset_of_mem_nsmul_image

set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Pointwise
open Erdos338Proof
variable {G : Type*} [AddCommGroup G] [DecidableEq G]
namespace Erdos338Proof
theorem _root_.solution {A : Finset ℕ} {ℓ h m x : ℕ} [NeZero ℓ]
    (hA0 : 0 ∈ A) (hAℓ : ℓ ∈ A) (hle : ∀ a ∈ A, a ≤ ℓ)
    (huniv : h • A.image (Nat.castAddMonoidHom (ZMod ℓ)) = univ)
    (hx1 : h * ℓ ≤ x) (hx2 : x + h * ℓ ≤ m * ℓ) :
    ∃ M : Multiset ℕ, M.card = m ∧ (∀ a ∈ M, a ∈ A) ∧ M.sum = x := by
  have hℓ : 0 < ℓ := Nat.pos_of_ne_zero (NeZero.ne ℓ)
  obtain ⟨M₀, hc, hA, hs⟩ := exists_multiset_of_mem_nsmul_image
    (huniv ▸ Finset.mem_univ (x : ZMod ℓ))
  simp only [Nat.coe_castAddMonoidHom] at hs
  have hsum : M₀.sum ≤ h * ℓ := by
    rw [← hc]
    exact Multiset.sum_le_card_nsmul _ _ fun a ha ↦ hle a (hA a ha)
  have hmod : M₀.sum ≡ x [MOD ℓ] := (ZMod.natCast_eq_natCast_iff _ _ _).1 hs
  obtain ⟨j, hj⟩ : ℓ ∣ x - M₀.sum := (Nat.modEq_iff_dvd' (by omega)).1 hmod
  have hjm : h + j ≤ m := by
    have : j * ℓ ≤ x := by rw [mul_comm]; omega
    by_contra hcon
    have : m * ℓ < (h + j) * ℓ := Nat.mul_lt_mul_of_pos_right (by omega) hℓ
    nlinarith
  refine ⟨M₀ + Multiset.replicate j ℓ + Multiset.replicate (m - (h + j)) 0, ?_, ?_, ?_⟩
  · simp [hc]; omega
  · intro a ha
    simp only [Multiset.mem_add, Multiset.mem_replicate] at ha
    rcases ha with (ha | ⟨_, rfl⟩) | ⟨_, rfl⟩
    · exact hA a ha
    · exact hAℓ
    · exact hA0
  · simp only [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, mul_zero, add_zero]
    rw [mul_comm j ℓ, ← hj]
    omega
end Erdos338Proof
