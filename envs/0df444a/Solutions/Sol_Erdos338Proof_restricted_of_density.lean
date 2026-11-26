-- Prove2me | solution 1 for Erdos338Proof.restricted_of_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:09:31.808556+00:00
-- url     : https://prove2.me/submissions/099ba0fc-8b99-4ce2-8476-fd3401fb4e62

module
public import Definitions.Def_Erdos338_Pairs
public import Definitions.Def_Erdos338_Residue
public import Definitions.Def_Erdos338_Shift
public import Definitions.Def_Erdos338_Main
public import Theorems.Thm_Erdos338Proof_greedy
public import Theorems.Thm_Erdos338Proof_pairs_dense
public import Theorems.Thm_Erdos338Proof_residue_uniform
public import Theorems.Thm_Erdos338Proof_usl


set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos338Proof
namespace Erdos338Proof
theorem _root_.solution (A : Set ℕ)
    (hres : ∀ Q, 0 < Q → ∀ c, ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ A) ∧ ∑ x ∈ S, x ≡ c [MOD Q])
    {δ : ℝ} (hδ : 0 < δ) {N₀ : ℕ} (hN₀ : ∀ b ≥ N₀, δ * b ≤ cnt A b) :
    ∃ t, ∀ᶠ n in Filter.atTop, ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ A) ∧ #S ≤ t ∧ ∑ x ∈ S, x = n := by
  classical
  have hγ : 0 < δ ^ 2 / 8 := by positivity
  obtain ⟨K, hK⟩ := usl hγ
  have hQ : 0 < K ! := Nat.factorial_pos K
  obtain ⟨B, T, hBT⟩ := residue_uniform hQ (hres _ hQ)
  set R := 2 * (B + 2 * K) + 1 with hR
  obtain ⟨d, b₀, N', hd1, hdK, hcov⟩ := hK {m | R ≤ #(rep A m)} (pairs_dense hδ hN₀ R)
  have hdQ : d ∣ K ! := Nat.dvd_factorial hd1 hdK
  refine ⟨B + 2 * K, Filter.eventually_atTop.2 ⟨T + K * b₀ + d * N', fun n hn ↦ ?_⟩⟩
  obtain ⟨S₀, hS₀A, hS₀B, hS₀T, hS₀c⟩ := hBT (n - K * b₀)
  set s₀ := ∑ x ∈ S₀, x with hs₀
  have hmod : s₀ ≡ n - K * b₀ [MOD d] := Nat.ModEq.of_dvd hdQ hS₀c
  obtain ⟨x, hx⟩ := (Nat.modEq_iff_dvd' (by omega)).1 hmod
  have hxN : N' ≤ x := by
    by_contra h
    push Not at h
    have : d * x < d * N' := Nat.mul_lt_mul_of_pos_left h hd1
    omega
  obtain ⟨Ms, hMs1, hMs2, hMs3⟩ := hcov x hxN
  obtain ⟨Sp, hdisj, hSpA, hSpc, hSps⟩ := greedy A S₀ Ms fun m hm ↦ by
    have h : R ≤ #(rep A m) := hMs2 m hm
    rw [hMs1]
    omega
  refine ⟨S₀ ∪ Sp, fun y hy ↦ ?_, ?_, ?_⟩
  · rcases mem_union.1 hy with hy | hy
    exacts [hS₀A y hy, hSpA y hy]
  · rw [card_union_of_disjoint hdisj, hSpc, hMs1]
    omega
  · rw [sum_union hdisj, hSps, hMs3]
    omega
end Erdos338Proof
