-- Prove2me | solution 1 for Corless.Dv_fold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:43:19.680604+00:00
-- url     : https://prove2.me/submissions/8bc33d16-278c-473c-8ef1-72197eb54ec9

module
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Tactic.LinearCombination
public import Definitions.Def_LeanPool_CorlessNilpotent_Path
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity
public import Theorems.Thm_Corless_Dv_congr
public import Theorems.Thm_Corless_Dv_one
public import Theorems.Thm_Corless_Dv_reverse
public import Theorems.Thm_Corless_Dv_split
public import Theorems.Thm_Corless_Dv_succ_succ_left
public import Theorems.Thm_Corless_Dv_zero
attribute [local simp] Corless.Dv_one
attribute [local simp] Corless.Dv_zero



set_option autoImplicit true
@[expose] public section
public section
open Polynomial Finset
open Corless
namespace Corless
theorem _root_.solution (s : ℕ → ℤ) (n : ℕ) (h : IsFolded s n) :
    Dv s (2 * n + 3) = Dv s (n + 1) ^ 2 := by
  obtain ⟨hmid, hmir⟩ := h
  have suffix (m a : ℕ) (hm : m ≤ n + 1) (ha : a + m = 2 * n + 3) :
      Dv (fun i => s (i + a)) m = Dv s m := by
    rw [← Dv_reverse s m]
    apply Dv_congr
    intro i hi
    have agree := hmir (m - 2 - i) (by omega)
    rwa [show 2 * n + 1 - (m - 2 - i) = i + a by omega] at agree
  have hsplit := Dv_split s n (n + 1)
  rw [show n + (n + 1) + 2 = 2 * n + 3 by omega] at hsplit
  simp only [Nat.add_assoc] at hsplit
  have hleft := Dv_succ_succ_left (fun i => s (i + n + 1)) n
  simp_rw [Nat.zero_add, show ∀ i : ℕ, i + 2 + n + 1 = i + (n + 3) by intro i; omega,
    show ∀ i : ℕ, i + 1 + n + 1 = i + (n + 2) by intro i; omega] at hleft
  simp only [Nat.add_assoc] at hleft
  rw [hsplit, hleft, suffix (n + 1) (n + 2) le_rfl (by omega),
    suffix n (n + 3) (by omega) (by omega), hmid, C_neg]
  ring
end Corless
