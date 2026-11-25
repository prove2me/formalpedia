-- Prove2me | solution 1 for Erdos393Proof.shape_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:55:10.72666+00:00
-- url     : https://prove2.me/submissions/ac8458b1-f870-4a4e-9a94-82883d71ba53

module
public import Mathlib
public import Definitions.Def_Erdos393Palomar_Solution
public import Theorems.Thm_Erdos393Proof_core
public import Theorems.Thm_Erdos393Proof_poly_shape

set_option autoImplicit true
@[expose] public section
public section
open Filter Asymptotics
open scoped Nat
open Erdos393Proof
open ABC Polynomial
namespace Erdos393Proof
theorem _root_.solution (habc : AbcHyp)
    (T : Finset ℕ) (h0 : 0 ∈ T) {m : ℕ} (hm : m ∈ T) (hm0 : m ≠ 0) :
    ∃ K X : ℕ, ∀ a n : ℕ, ∏ i ∈ T, (a + i) = n ! → n ! ≤ K * X ^ n := by
  obtain ⟨k, R, hR0, hdeg, hid⟩ := poly_shape T h0 hm hm0
  obtain ⟨K, X, hKX⟩ := core habc T.card k R hR0 hdeg
  have hpos : 0 < T.card := Finset.card_pos.2 ⟨m, hm⟩
  refine ⟨K, X, fun a n h ↦ hKX (T.card * a + ∑ i ∈ T, i) n ?_ ?_ ?_⟩
  · have : m ≤ ∑ i ∈ T, i := Finset.single_le_sum (fun i _ ↦ Nat.zero_le i) hm
    omega
  · rw [← h]
    exact Finset.prod_le_pow_card _ _ _ fun i hi ↦
      Nat.add_le_add (Nat.le_mul_of_pos_left a hpos)
        (Finset.single_le_sum (fun i _ ↦ Nat.zero_le i) hi)
  · have := hid a
    rw [h] at this
    exact_mod_cast this
end Erdos393Proof
