-- Prove2me | solution 1 for CompOT.Vertices.prop_3_4_perturbation_feasible
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:03:19.273303+00:00
-- url     : https://prove2.me/submissions/7676212a-1ecd-40c4-b99d-b8e2e48cde03

import Mathlib
import Definitions.Def_CompOT_Vertices_Defs

set_option autoImplicit false
open CompOT.Vertices Filter Topology

theorem solution {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ)
    (P E : Matrix (Fin n) (Fin m) ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (hP : P ∈ CompOT.Assignment.couplings a b)
    (hrow : ∀ i, ∑ j, E i j = 0) (hcol : ∀ j, ∑ i, E i j = 0)
    (hsupp : ∀ i j, E i j ≠ 0 → 0 < P i j) :
    ∃ t : ℝ, 0 < t ∧ P + t • E ∈ CompOT.Assignment.couplings a b ∧
      P - t • E ∈ CompOT.Assignment.couplings a b := by
  obtain ⟨hP0, hPr, hPc⟩ := hP
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i j, t * |E i j| ≤ P i j := by
    rw [Filter.eventually_all]; intro i
    rw [Filter.eventually_all]; intro j
    by_cases h : E i j = 0
    · simp [h, hP0 i j]
    · have habs : 0 < |E i j| := abs_pos.2 h
      have hlt : (0 : ℝ) < P i j / |E i j| := div_pos (hsupp i j h) habs
      have : ∀ᶠ t in 𝓝 (0 : ℝ), t < P i j / |E i j| := Iio_mem_nhds hlt
      filter_upwards [nhdsWithin_le_nhds this] with t ht
      rw [lt_div_iff₀ habs] at ht
      exact ht.le
  obtain ⟨t, ht, htpos⟩ := (hev.and self_mem_nhdsWithin).exists
  have htp : 0 < t := htpos
  refine ⟨t, htp, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · intro i j
    have := ht i j
    have h2 := neg_abs_le (E i j)
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left h2 htp.le]
  · intro i
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hrow, hPr, mul_zero, add_zero]
  · intro j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hcol, hPc, mul_zero, add_zero]
  · intro i j
    have := ht i j
    have h2 := le_abs_self (E i j)
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left h2 htp.le]
  · intro i
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hrow, hPr, mul_zero, sub_zero]
  · intro j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hcol, hPc, mul_zero, sub_zero]
