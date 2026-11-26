-- Prove2me | solution 1 for Erdos338Proof.pairs_dense
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:02:27.99007+00:00
-- url     : https://prove2.me/submissions/d354251d-52ce-449e-b5c7-7a5027a39ba4

module
public import Definitions.Def_Erdos338_Structure
public import Definitions.Def_Erdos338_Pairs
public import Theorems.Thm_Erdos338Proof_pair_count
public import Theorems.Thm_Erdos338Proof_cnt_le_of_subset


set_option autoImplicit true
@[expose] public section
public section
open Finset
open Erdos338Proof
namespace Erdos338Proof
theorem _root_.solution {δ : ℝ} (hδ : 0 < δ) {A : Set ℕ} {N₀ : ℕ}
    (hN₀ : ∀ b ≥ N₀, δ * b ≤ cnt A b) (R : ℕ) :
    ∃ N, ∀ b ≥ N, δ ^ 2 / 8 * b ≤ cnt {m | R ≤ #(rep A m)} b := by
  set q := ⌈(4 + 8 * (R : ℝ)) / δ ^ 2⌉₊ with hq
  refine ⟨2 * N₀ + q + 5, fun b hb ↦ ?_⟩
  set L := b / 2 with hLdef
  have hL1 : 2 * L ≤ b := by omega
  have hL2 : b ≤ 2 * L + 1 := by omega
  have hmain := pair_count A R hL1
  set k := cnt A L
  set c := cnt {m | R ≤ #(rep A m)} b
  have hk : δ * L ≤ k := hN₀ L (by omega)
  have hkL : k ≤ L := cnt_le_of_subset fun _ _ hx ↦ hx
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hceil : (4 + 8 * (R : ℝ)) / δ ^ 2 ≤ (b : ℝ) - 4 := by
    have h1 := Nat.le_ceil ((4 + 8 * (R : ℝ)) / δ ^ 2)
    have h2 : (q : ℝ) + 4 ≤ b := by exact_mod_cast (by omega : q + 4 ≤ b)
    linarith
  have hR : 4 + 8 * (R : ℝ) ≤ δ ^ 2 * ((b : ℝ) - 4) := by
    have := mul_le_mul_of_nonneg_left hceil hδ2.le
    rwa [mul_div_cancel₀ _ hδ2.ne'] at this
  have hb4 : (4 : ℝ) ≤ b := by
    have : (0 : ℝ) ≤ (4 + 8 * (R : ℝ)) / δ ^ 2 := by positivity
    linarith
  have hmainR : (k : ℝ) * k ≤ b * c + b * R + k := by exact_mod_cast hmain
  have hLr1 : (2 * L : ℝ) ≤ b := by exact_mod_cast hL1
  have hLr2 : (b : ℝ) ≤ 2 * L + 1 := by exact_mod_cast hL2
  have hkL' : (k : ℝ) ≤ L := by exact_mod_cast hkL
  have hk2 : δ ^ 2 * (L : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hk 2
  have hL3 : ((b : ℝ) - 1) ^ 2 ≤ 4 * (L : ℝ) ^ 2 := by
    have h0 : (0 : ℝ) ≤ b - 1 := by linarith
    have : ((b : ℝ) - 1) ^ 2 ≤ (2 * L) ^ 2 := pow_le_pow_left₀ h0 (by linarith) 2
    linarith
  have hL4 : δ ^ 2 * ((b : ℝ) - 1) ^ 2 ≤ δ ^ 2 * (4 * (L : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hL3 hδ2.le
  have hprod : (b : ℝ) * (4 + 8 * R) ≤ b * (δ ^ 2 * (b - 4)) :=
    mul_le_mul_of_nonneg_left hR (by positivity)
  have key : (b : ℝ) * (δ ^ 2 / 8 * b) ≤ b * c := by
    nlinarith
  have hbpos : (0 : ℝ) < b := by linarith
  exact le_of_mul_le_mul_left key hbpos
end Erdos338Proof
