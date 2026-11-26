-- Prove2me | solution 1 for Erdos338Proof.exists_mem_Ioc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:59:41.586971+00:00
-- url     : https://prove2.me/submissions/d74fc9f1-31ef-4458-879e-475a556eb9b9

module
public import Definitions.Def_Erdos338_Covering
public import Definitions.Def_Erdos338_Structure
public import Theorems.Thm_Erdos338Proof_cnt_le_of_subset

set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Pointwise
open Erdos338Proof
namespace Erdos338Proof
theorem _root_.solution {γ : ℝ} (hγ : 0 < γ) {C : ℕ} (hC : (2 / γ : ℝ) ≤ C) {E : Set ℕ} {N : ℕ}
    (hN : ∀ b ≥ N, γ * b ≤ cnt E b) {y : ℕ} (hyN : N ≤ y) (hy2 : 2 ≤ y) :
    ∃ ℓ ∈ E, y < ℓ ∧ ℓ ≤ C * y := by
  by_contra hcon
  push Not at hcon
  have hC1 : 1 ≤ C := by
    have : (0 : ℝ) < C := lt_of_lt_of_le (by positivity) hC
    exact_mod_cast this
  have hle : cnt E (C * y + 1) ≤ y + 1 := by
    apply cnt_le_of_subset
    intro x hx hxb
    by_contra hxy
    exact absurd (hcon x hx (by omega)) (by omega)
  have hb : N ≤ C * y + 1 := by nlinarith
  have h1 := hN _ hb
  have h2 : (cnt E (C * y + 1) : ℝ) ≤ y + 1 := by exact_mod_cast hle
  have h3 : (2 : ℝ) ≤ γ * C := by
    have := mul_le_mul_of_nonneg_left hC hγ.le
    rwa [mul_div_cancel₀ _ hγ.ne'] at this
  have hy : (2 : ℝ) ≤ y := by exact_mod_cast hy2
  push_cast at h1
  nlinarith
end Erdos338Proof
