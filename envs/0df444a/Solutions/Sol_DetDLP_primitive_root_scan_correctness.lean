-- Prove2me | solution 1 for DetDLP.primitive_root_scan_correctness
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T11:52:55.051349+00:00
-- url     : https://prove2.me/submissions/db543cdb-4295-4fc9-8a50-f3552bbcdfa3

import Mathlib
import Definitions.Def_DetDLP_FactorBase
import Theorems.Thm_DetDLP_primitive_root_from_generating_set

set_option autoImplicit false

open DetDLP

theorem solution :
    ∀ (p m : ℕ) [Fact p.Prime] (F : Fin m → List (ZMod p)ˣ),
      (∀ π ∈ (p - 1).primeFactors, ∃ i : Fin m, ∃ u ∈ F i, u ^ ((p - 1) / π) ≠ 1) →
      let U : List (ZMod p)ˣ := (List.ofFn F).flatten
      let a : ℕ → (ZMod p)ˣ := fun π =>
        (U.find? (fun u => decide (u ^ ((p - 1) / π) ≠ 1))).getD 1
      let h : (ZMod p)ˣ :=
        ∏ π ∈ (p - 1).primeFactors,
          (a π) ^ ((p - 1) / π ^ (p - 1).factorization π)
      (∀ π ∈ (p - 1).primeFactors, (a π) ^ ((p - 1) / π) ≠ 1) ∧
      orderOf h = p - 1 ∧
      (p - 1).primeFactors.card ≤ bitLen p ∧
      (p - 1).primeFactors.card * U.length ≤ bitLen p * (∑ i : Fin m, (F i).length) := by
  intro p m _ F hwit U a h
  have hp : p.Prime := Fact.out
  have hU_len : U.length = ∑ i : Fin m, (F i).length := by
    dsimp only [U]
    rw [List.length_flatten, List.map_ofFn]
    exact List.sum_ofFn
  have ha : ∀ π ∈ (p - 1).primeFactors, (a π) ^ ((p - 1) / π) ≠ 1 := by
    intro π hπ
    obtain ⟨i, u, hu_mem, hu_prop⟩ := hwit π hπ
    have huU : u ∈ U := by
      dsimp only [U]
      rw [List.mem_flatten]
      exact ⟨F i, List.mem_ofFn.mpr ⟨i, rfl⟩, hu_mem⟩
    dsimp only [a]
    cases hfind : U.find? (fun u : (ZMod p)ˣ => decide (u ^ ((p - 1) / π) ≠ 1)) with
    | none =>
      have hnone := List.find?_eq_none.mp hfind u huU
      simp only [decide_eq_true_eq] at hnone
      exact absurd hu_prop hnone
    | some v =>
      have hsome := List.find?_some hfind
      simp only [decide_eq_true_eq] at hsome
      simpa using hsome
  have hord : orderOf h = p - 1 := by
    let Ftriv : Fin 1 → List (ZMod p)ˣ := fun _ => (Finset.univ : Finset (ZMod p)ˣ).toList
    have hcov : ∀ X : (ZMod p)ˣ, ∃ A B : Fin 1 → (ZMod p)ˣ,
        (∀ i : Fin 1, A i ∈ Ftriv i ∧ B i ∈ Ftriv i) ∧ (∏ i : Fin 1, (A i * B i)) = X := by
      intro X
      refine ⟨fun _ => X, fun _ => 1, fun _ => ⟨by simp [Ftriv], by simp [Ftriv]⟩, by simp⟩
    exact (DetDLP.primitive_root_from_generating_set p 1 Ftriv hcov).2 a ha
  have hcard_le : (p - 1).primeFactors.card ≤ bitLen p := by
    by_cases hp2 : p = 2
    · subst hp2
      simp [bitLen]
    · have hp3 : 3 ≤ p := by have := hp.two_le; omega
      have hpm1_pos : 0 < p - 1 := by omega
      have h2pow : 2 ^ (p - 1).primeFactors.card ≤ ∏ π ∈ (p - 1).primeFactors, π := by
        rw [← Finset.prod_const]
        refine Finset.prod_le_prod' fun π hπ => ?_
        exact (Nat.prime_of_mem_primeFactors hπ).two_le
      have hprod_le : ∏ π ∈ (p - 1).primeFactors, π ≤ p - 1 :=
        Nat.le_of_dvd hpm1_pos (Nat.prod_primeFactors_dvd (p - 1))
      have hp_le_pow : p ≤ 2 ^ bitLen p := Nat.le_pow_clog (by decide : 1 < 2) p
      have hlt_pow : 2 ^ (p - 1).primeFactors.card < 2 ^ bitLen p := by omega
      exact le_of_lt ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlt_pow)
  refine ⟨ha, hord, hcard_le, ?_⟩
  rw [hU_len]
  exact Nat.mul_le_mul_right _ hcard_le
