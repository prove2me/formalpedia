-- Prove2me | solution 1 for Corless.Dv_parity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:42:22.007187+00:00
-- url     : https://prove2.me/submissions/8623af77-3bc6-4033-a368-d19076c7036f

module
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Tactic.LinearCombination
public import Definitions.Def_LeanPool_CorlessNilpotent_Path
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity
public import Theorems.Thm_Corless_f_succ_succ
public import Theorems.Thm_Corless_IsSign_mono
public import Theorems.Thm_Corless_Dv_one
public import Theorems.Thm_Corless_Dv_succ_succ
public import Theorems.Thm_Corless_Dv_zero
attribute [local simp] Corless.Dv_one
attribute [local simp] Corless.Dv_zero



set_option autoImplicit true
@[expose] public section
public section
open Polynomial Finset
open Corless
namespace Corless
theorem _root_.solution {s : ℕ → ℤ} : ∀ j, IsSign s j → ∃ R : ℤ[X], Dv s j = f j + 2 * R
  | 0, _ => ⟨0, by simp [f]⟩
  | 1, _ => ⟨0, by simp [f]⟩
  | j + 2, hs => by
      obtain ⟨R1, h1⟩ := solution (j + 1) (hs.mono (by omega))
      obtain ⟨R0, h0⟩ := solution j (hs.mono (by omega))
      rcases hs j (by omega) with h | h
      · exact ⟨R1 + X * R0, by rw [Dv_succ_succ, f_succ_succ, h1, h0, h]; simp; ring⟩
      · exact ⟨R1 - X * f j - X * R0, by rw [Dv_succ_succ, f_succ_succ, h1, h0, h]; simp; ring⟩
end Corless
