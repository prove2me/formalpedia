-- Prove2me | solution 1 for Conway99Formal.CubicMetric.minSquares_attained
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T04:08:00.068983+00:00
-- url     : https://prove2.me/submissions/e457e771-b9ec-49f9-a61f-fbae4516a37d

import Definitions.Def_Arithmetic
import Mathlib

namespace Conway99Formal.CubicMetric
end Conway99Formal.CubicMetric

set_option autoImplicit false

namespace Conway99Formal.CubicMetric





private theorem balanced_configuration {ι : Type*} [DecidableEq ι]
    (s t : Finset ι) (ht : t ⊆ s) (q : ℤ) :
    ∃ x : ι → ℤ,
      (∑ i ∈ s, x i) = (s.card : ℤ) * q + t.card ∧
      (∑ i ∈ s, (x i) ^ 2) =
        (s.card : ℤ) * q ^ 2 + (2 * q + 1) * t.card := by
  classical
  let b : ι → ℤ := fun i => if i ∈ t then 1 else 0
  let x : ι → ℤ := fun i => q + b i
  have hb : (∑ i ∈ s, b i) = (t.card : ℤ) := by
    have hinter : s ∩ t = t := Finset.inter_eq_right.mpr ht
    simp [b, hinter]
  have hsum : (∑ i ∈ s, x i) = (s.card : ℤ) * q + t.card := by
    simp [x, Finset.sum_add_distrib, hb]
  have hsq (i : ι) : (x i) ^ 2 = q ^ 2 + (2 * q + 1) * b i := by
    by_cases hi : i ∈ t
    · simp [x, b, hi]
      ring
    · simp [x, b, hi]
  have hsumSq : (∑ i ∈ s, (x i) ^ 2) =
      (s.card : ℤ) * q ^ 2 + (2 * q + 1) * t.card := by
    simp_rw [hsq]
    simp [Finset.sum_add_distrib, ← Finset.mul_sum, hb]
  exact ⟨x, hsum, hsumSq⟩








































end Conway99Formal.CubicMetric

set_option autoImplicit false

open Conway99Formal.CubicMetric

open Conway99Formal.CubicMetric in
theorem solution {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (total : ℤ) (hs : s.Nonempty) :
    ∃ x : ι → ℤ,
      (∑ i ∈ s, x i) = total ∧
      (∑ i ∈ s, (x i) ^ 2) = minSquares s.card total := by
  let m : ℤ := s.card
  let q : ℤ := total / m
  let r : ℤ := total % m
  let rn : ℕ := r.toNat
  have hmpos : 0 < m := by
    dsimp [m]
    exact_mod_cast Finset.card_pos.mpr hs
  have hr0 : 0 ≤ r := Int.emod_nonneg total (by omega)
  have hrlt : r < m := Int.emod_lt_of_pos total hmpos
  have hrcast : (rn : ℤ) = r := Int.toNat_of_nonneg hr0
  have hrle : rn ≤ s.card := by omega
  obtain ⟨t, ht, hcard⟩ := Finset.exists_subset_card_eq hrle
  obtain ⟨x, hsum, hsq⟩ := balanced_configuration s t ht q
  refine ⟨x, ?_, ?_⟩
  · calc
      (∑ i ∈ s, x i) = m * q + (t.card : ℤ) := hsum
      _ = m * (total / m) + r := by rw [hcard]; simp [q, hrcast]
      _ = total := Int.mul_ediv_add_emod total m
  · calc
      (∑ i ∈ s, (x i) ^ 2) = m * q ^ 2 + (2 * q + 1) * t.card := hsq
      _ = minSquares s.card total := by rw [hcard]; simp [minSquares, m, q, r, hrcast]
