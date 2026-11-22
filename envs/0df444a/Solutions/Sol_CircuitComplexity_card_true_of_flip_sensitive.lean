-- Prove2me | solution 1 for CircuitComplexity.card_true_of_flip_sensitive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:11:50.816378+00:00
-- url     : https://prove2.me/submissions/5640eca4-7d56-4864-b500-c7f80de59173

module
public import Definitions.Def_LeanPool_CircuitComplexity_NF_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_NF
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth



set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit true
set_option autoImplicit true
open CircuitComplexity
namespace CircuitComplexity
theorem _root_.solution {N : Nat} (hN : 1 ≤ N)
    (f : BitString N → Bool)
    (hflip : ∀ x (i : Fin N), f (Function.update x i (!x i)) = !f x) :
    (Finset.univ.filter (fun x => f x = true)).card = 2 ^ (N - 1) := by
  set S_true := Finset.univ.filter (fun x => f x = true)
  set S_false := Finset.univ.filter (fun x => f x = false)
  -- The involution: flip variable 0
  have hN' : 0 < N := by omega
  set flip0 : BitString N → BitString N := fun x => Function.update x ⟨0, hN'⟩ (!x ⟨0, hN'⟩)
  -- flip0 is self-inverse
  have flip0_inv : ∀ x, flip0 (flip0 x) = x := by
    intro x; ext j; simp only [flip0]
    simp_all
  -- flip0 maps true-set to false-set
  have flip0_tf : ∀ x, f x = true → f (flip0 x) = false := by
    intro x hx; have := hflip x ⟨0, hN'⟩; rw [hx] at this; simpa using this
  -- Bijection from S_true to S_false
  have hcard_eq : S_true.card = S_false.card := by
    apply Finset.card_bij (fun x _ => flip0 x)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, S_true, S_false] at hx ⊢
      exact flip0_tf x hx
    · intro a₁ h₁ a₂ h₂ heq
      have := congr_arg flip0 heq
      rwa [flip0_inv, flip0_inv] at this
    · intro b hb
      refine ⟨flip0 b, ?_, flip0_inv b⟩
      simp only [S_true, S_false, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      -- f b = false, need f (flip0 b) = true
      have h1 := hflip b ⟨0, hN'⟩
      rwa [hb, Bool.not_false] at h1
  -- |S_true| + |S_false| = 2^N
  have hcard_total : S_true.card + S_false.card = 2 ^ N := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun x : BitString N => f x = true)
    simp only [Finset.card_univ] at h
    rw [show Fintype.card (BitString N) = 2 ^ N from by
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]] at h
    convert h using 2
    simp only [S_false]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases f x <;> simp
  -- 2 * S_true.card = 2^N, so S_true.card = 2^{N-1}
  have : 2 ^ N = 2 * 2 ^ (N - 1) := by
    cases N with
    | zero => omega
    | succ n => simp [Nat.pow_succ, Nat.mul_comm]
  omega
end CircuitComplexity
