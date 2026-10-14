-- Prove2me | solution 1 for Disjunctive.MonoidalStrengthening.monoidal_strengthening_validity_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T22:51:20.776977+00:00
-- url     : https://prove2.me/submissions/c074d780-d66c-4eee-b82b-fca1ee147aae

import Mathlib
import Definitions.Def_Disjunctive_MonoidalStrengthening_Basic



namespace Disjunctive.MonoidalStrengthening

theorem msv_core {q n : ℕ}
    (a : Fin q → Fin n → ℝ) (a0 b : Fin q → ℝ) (hb : ∀ i, b i ≤ a0 i) (J1 : Finset (Fin n))
    (m : Fin n → Fin q → ℤ) (hm_mem : ∀ j ∈ J1, (fun i => m j i) ∈ CutMonoid q)
    (x : Fin n → ℝ) (hx_nonneg : 0 ≤ x) (hx_int : ∀ j ∈ J1, ∃ k : ℤ, x j = (k : ℝ))
    (hx_lb : ∀ i, b i ≤ ∑ j, a i j * x j)
    (hx_disj : ∃ i, a0 i ≤ ∑ j, a i j * x j) :
    ∃ i, a0 i ≤ ∑ j ∈ J1, (a i j + (a0 i - b i) * (m j i : ℝ)) * x j +
      ∑ j ∈ Finset.univ \ J1, a i j * x j := by
  classical
  set s : Fin q → ℝ := fun i => ∑ j ∈ J1, (m j i : ℝ) * x j with hs
  have hsplit : ∀ i, ∑ j ∈ J1, (a i j + (a0 i - b i) * (m j i : ℝ)) * x j +
      ∑ j ∈ Finset.univ \ J1, a i j * x j = ∑ j, a i j * x j + (a0 i - b i) * s i := by
    intro i
    have h1 := Finset.sum_sdiff (f := fun j => a i j * x j) (Finset.subset_univ J1)
    rw [← h1, hs]
    simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    have : ∀ j ∈ J1, (a0 i - b i) * (m j i : ℝ) * x j = (a0 i - b i) * ((m j i : ℝ) * x j) :=
      fun j _ => by ring
    rw [Finset.sum_congr rfl this]
    ring
  let kf : Fin n → ℤ := fun j => if h : j ∈ J1 then Classical.choose (hx_int j h) else 0
  have hsint : ∀ i, s i = ((∑ j ∈ J1, m j i * kf j : ℤ) : ℝ) := by
    intro i
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    simp only [kf, dif_pos hj]
    rw [← Classical.choose_spec (hx_int j hj)]
  by_contra hcon
  push_neg at hcon
  have hle : ∀ i, s i ≤ 0 := by
    intro i
    by_contra hpos
    push_neg at hpos
    rw [hsint i] at hpos
    have h1 : (1 : ℤ) ≤ ∑ j ∈ J1, m j i * kf j := by exact_mod_cast hpos
    have h1' : (1 : ℝ) ≤ s i := by rw [hsint i]; exact_mod_cast h1
    have := hcon i
    rw [hsplit i] at this
    have := hx_lb i
    have := hb i
    nlinarith
  have hsum : 0 ≤ ∑ i, s i := by
    simp only [hs]
    rw [Finset.sum_comm]
    apply Finset.sum_nonneg
    intro j hj
    rw [← Finset.sum_mul]
    apply mul_nonneg
    · have := hm_mem j hj
      simp only [CutMonoid, Set.mem_setOf_eq] at this
      exact_mod_cast this
    · exact hx_nonneg j
  have hzero : ∀ i, s i = 0 := by
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonpos (fun i _ => hle i)).mp
      (le_antisymm (Finset.sum_nonpos (fun i _ => hle i)) hsum) i (Finset.mem_univ _)
    exact this
  obtain ⟨i, hi⟩ := hx_disj
  have := hcon i
  rw [hsplit i, hzero i] at this
  linarith

end Disjunctive.MonoidalStrengthening

open Disjunctive.MonoidalStrengthening


theorem solution {q n : ℕ}
    (a : Fin q → Fin n → ℝ) (a0 b : Fin q → ℝ) (hb : ∀ i, b i ≤ a0 i) (J1 : Finset (Fin n))
    (m : Fin n → Fin q → ℤ) (hm_mem : ∀ j ∈ J1, (fun i => m j i) ∈ CutMonoid q)
    (x : Fin n → ℝ) (hx_nonneg : 0 ≤ x) (hx_int : ∀ j ∈ J1, ∃ k : ℤ, x j = (k : ℝ))
    (hx_lb : ∀ i, b i ≤ ∑ j, a i j * x j)
    (hx_disj : ∃ i, a0 i ≤ ∑ j, a i j * x j) :
    ∃ i, a0 i ≤ ∑ j ∈ J1, (a i j + (a0 i - b i) * (m j i : ℝ)) * x j +
      ∑ j ∈ Finset.univ \ J1, a i j * x j := by
  exact msv_core a a0 b hb J1 m hm_mem x hx_nonneg hx_int hx_lb hx_disj
