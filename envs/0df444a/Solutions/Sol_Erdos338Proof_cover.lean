-- Prove2me | solution 1 for Erdos338Proof.cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:06:09.464221+00:00
-- url     : https://prove2.me/submissions/3bd228ab-b02c-46ee-b8e4-b5ee781fab01

module
public import Definitions.Def_Erdos338_Covering
public import Definitions.Def_Erdos338_Structure
public import Theorems.Thm_Erdos338Proof_dense_step
public import Theorems.Thm_Erdos338Proof_exists_mem_Ioc

set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Pointwise
open Erdos338Proof
namespace Erdos338Proof
theorem _root_.solution {γ : ℝ} (hγ : 0 < γ) : ∃ K : ℕ, (2 / γ : ℝ) < K ∧ ∀ E : Set ℕ, 0 ∈ E →
    (∃ F : Finset ℕ, (F : Set ℕ) ⊆ E ∧ (1 : ℤ) ∈ Submodule.span ℤ ((Nat.cast : ℕ → ℤ) '' F)) →
    (∃ N, ∀ b ≥ N, γ * b ≤ cnt E b) →
    ∃ N', ∀ x ≥ N', ∃ M : Multiset ℕ, M.card = K ∧ (∀ a ∈ M, a ∈ E) ∧ M.sum = x := by
  set h : ℕ := ⌈4 / γ⌉₊ + 1 with hhdef
  set C : ℕ := ⌈2 / γ⌉₊ + 1 with hCdef
  have hh : (4 / γ : ℝ) < h := by
    rw [hhdef]; push_cast; linarith [Nat.le_ceil (4 / γ)]
  have hC : (2 / γ : ℝ) ≤ C := by
    rw [hCdef]; push_cast; linarith [Nat.le_ceil (2 / γ)]
  have hh1 : 1 ≤ h := by omega
  have hC1 : 1 ≤ C := by omega
  refine ⟨h * (C + 1), ?_, ?_⟩
  · have : (h : ℝ) ≤ h * (C + 1) := by
      have : (1 : ℝ) ≤ C + 1 := by linarith [(Nat.cast_nonneg C : (0 : ℝ) ≤ C)]
      nlinarith [(Nat.cast_nonneg h : (0 : ℝ) ≤ h)]
    have h42 : (2 / γ : ℝ) < 4 / γ := by
      apply div_lt_div_of_pos_right (by norm_num) hγ
    push_cast
    linarith
  rintro E hE0 ⟨F, hFE, h1⟩ ⟨N, hN⟩
  set L : ℕ := N + F.sup id + ⌈2 / γ⌉₊ + 2 with hL
  refine ⟨h * C * (L + 1), fun x hx ↦ ?_⟩
  have hhC : 0 < h * C := Nat.mul_pos (by omega) (by omega)
  set y := x / (h * C) with hy
  have hyL : L + 1 ≤ y := by
    rw [hy]
    exact (Nat.le_div_iff_mul_le hhC).2 (by rw [mul_comm]; exact hx)
  obtain ⟨ℓ, hℓE, hyℓ, hℓy⟩ := exists_mem_Ioc hγ hC hN (y := y) (by omega) (by omega)
  have hℓγ : (2 / γ : ℝ) ≤ ℓ := by
    have : ⌈2 / γ⌉₊ ≤ ℓ := by omega
    exact (Nat.le_ceil _).trans (by exact_mod_cast this)
  apply dense_step hγ hh hFE h1 hN hE0 hℓE (by omega) (by omega) hℓγ
  · -- `h ℓ ≤ h C y ≤ x`
    calc h * ℓ ≤ h * (C * y) := Nat.mul_le_mul_left h hℓy
      _ = y * (h * C) := by ring
      _ ≤ x := Nat.div_mul_le_self x (h * C)
  · -- `x < h C (y + 1) ≤ h C ℓ`
    have hx' : x < (y + 1) * (h * C) := by rw [hy, mul_comm]; exact Nat.lt_mul_div_succ x hhC
    have : (y + 1) * (h * C) ≤ ℓ * (h * C) := Nat.mul_le_mul_right _ hyℓ
    nlinarith
end Erdos338Proof
