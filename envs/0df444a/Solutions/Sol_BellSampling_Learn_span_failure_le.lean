-- Prove2me | solution 1 for BellSampling.Learn.span_failure_le
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:34:38.901962+00:00
-- url     : https://prove2.me/submissions/8bc5754d-d4da-4908-a831-476d663f76da

import Mathlib
import Definitions.Def_StabilizerRank
import Definitions.Def_BellSampling_Learn_Setting
open StabilizerRank

namespace Aux_Bell_span

lemma arith (n : ℕ) : (2 ^ n - 1) * 2 ^ n * 2 ^ ((n - 1) * (2 * n)) ≤ (2 ^ n) ^ (2 * n) := by
  cases n with
  | zero => simp
  | succ m =>
    have h1 : 2 ^ (m + 1) - 1 ≤ 2 ^ (m + 1) := Nat.sub_le _ _
    calc (2 ^ (m + 1) - 1) * 2 ^ (m + 1) * 2 ^ ((m + 1 - 1) * (2 * (m + 1)))
        ≤ 2 ^ (m + 1) * 2 ^ (m + 1) * 2 ^ ((m + 1 - 1) * (2 * (m + 1))) := by
          apply Nat.mul_le_mul_right; exact Nat.mul_le_mul_right _ h1
      _ = (2 ^ (m + 1)) ^ (2 * (m + 1)) := by
          rw [← pow_add, ← pow_add, ← pow_mul]
          congr 1
          simp only [Nat.add_sub_cancel]
          ring

end Aux_Bell_span

open BellSampling.Learn in
theorem solution {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (n : ℕ) (hV : Module.finrank (ZMod 2) V = n) :
    (Set.ncard {v : Fin (2 * n) → V | Submodule.span (ZMod 2) (Set.range v) ≠ ⊤} : ℝ) ≤
      1 / 2 ^ n * (Fintype.card V : ℝ) ^ (2 * n) := by
  classical
  haveI : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  have hcard : Fintype.card V = 2 ^ n := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hV]
  let D := Module.Dual (ZMod 2) V
  haveI : Finite D := Module.finite_of_finite (ZMod 2)
  haveI : Fintype D := Fintype.ofFinite D
  have hD : Nat.card D = 2 ^ n := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, Subspace.dual_finrank_eq, hV]
  -- kernel size
  have hker : ∀ f : D, f ≠ 0 → Nat.card (LinearMap.ker f) = 2 ^ (n - 1) := by
    intro f hf
    have hrange : Module.finrank (ZMod 2) (LinearMap.range f) = 1 := by
      have h1 : Module.finrank (ZMod 2) (LinearMap.range f) ≤ 1 := by
        have := Submodule.finrank_le (LinearMap.range f)
        simpa using this
      have h2 : Module.finrank (ZMod 2) (LinearMap.range f) ≠ 0 := by
        intro h0
        rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0
        exact hf h0
      omega
    have hrn := LinearMap.finrank_range_add_finrank_ker f
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    congr 1
    omega
  -- the sets A_f
  let A : {f : D // f ≠ 0} → Set (Fin (2 * n) → V) := fun f => {v | ∀ i, f.1 (v i) = 0}
  have hA : ∀ f, (A f).ncard = (2 ^ (n - 1)) ^ (2 * n) := by
    intro f
    rw [← Nat.card_coe_set_eq]
    change Nat.card {v : Fin (2 * n) → V // ∀ i, f.1 (v i) = 0} = _
    rw [Nat.card_congr (Equiv.subtypePiEquivPi (β := fun _ : Fin (2 * n) => V)
      (p := fun _ b => f.1 b = 0)), Nat.card_pi]
    have hk : Nat.card {b : V // f.1 b = 0} = 2 ^ (n - 1) := hker f.1 f.2
    simp only [hk, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsub : {v : Fin (2 * n) → V | Submodule.span (ZMod 2) (Set.range v) ≠ ⊤} ⊆ ⋃ f, A f := by
    intro v hv
    obtain ⟨f, hf, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hv)
    refine Set.mem_iUnion.mpr ⟨⟨f, hf⟩, fun i => ?_⟩
    have : v i ∈ Submodule.span (ZMod 2) (Set.range v) := Submodule.subset_span ⟨i, rfl⟩
    exact hle this
  have hnz : Fintype.card {f : D // f ≠ 0} = 2 ^ n - 1 := by
    have := Fintype.card_subtype_compl (fun f : D => f = 0)
    have hD' : Fintype.card D = 2 ^ n := by rw [Fintype.card_eq_nat_card]; exact hD
    rw [Fintype.card_subtype_eq, hD'] at this
    exact this
  have hbound : {v : Fin (2 * n) → V | Submodule.span (ZMod 2) (Set.range v) ≠ ⊤}.ncard ≤
      (2 ^ n - 1) * (2 ^ (n - 1)) ^ (2 * n) := by
    calc _ ≤ (⋃ f, A f).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ∑ f, (A f).ncard := Set.ncard_iUnion_le_of_fintype A
      _ = (2 ^ n - 1) * (2 ^ (n - 1)) ^ (2 * n) := by
        simp only [hA, Finset.sum_const, Finset.card_univ, hnz, smul_eq_mul]
  have hnat : {v : Fin (2 * n) → V | Submodule.span (ZMod 2) (Set.range v) ≠ ⊤}.ncard * 2 ^ n ≤
      (2 ^ n) ^ (2 * n) := by
    calc _ ≤ (2 ^ n - 1) * (2 ^ (n - 1)) ^ (2 * n) * 2 ^ n := Nat.mul_le_mul_right _ hbound
      _ = (2 ^ n - 1) * 2 ^ n * 2 ^ ((n - 1) * (2 * n)) := by rw [← pow_mul]; ring
      _ ≤ _ := Aux_Bell_span.arith n
  rw [hcard]
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [one_div, inv_mul_eq_div, le_div_iff₀ h2]
  exact_mod_cast hnat
