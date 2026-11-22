-- Prove2me | solution 1 for BiorthogonalSystem.topologicallyFree_iff_exists_biorthogonal
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T18:46:59.153793+00:00
-- url     : https://prove2.me/submissions/4424ced9-58a9-4a55-895a-841cf3d43cbe

import Mathlib

open Filter Topology Set

set_option autoImplicit false

theorem solution {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [LocallyConvexSpace ℝ E]
    {ι : Type*} (x : ι → E) :
    (∀ i : ι, x i ∉ (Submodule.span ℂ (x '' {j : ι | j ≠ i})).topologicalClosure) ↔
      ∃ u : ι → (E →L[ℂ] ℂ),
        (∀ i : ι, u i (x i) = 1) ∧ ∀ i j : ι, i ≠ j → u i (x j) = 0 := by
  constructor
  · intro hx
    have hSeparate (i : ι) : ∃ φ : E →L[ℂ] ℂ, φ (x i) = 1 ∧
        ∀ j : ι, i ≠ j → φ (x j) = 0 := by
      let S := Submodule.span ℂ (x '' {j : ι | j ≠ i})
      let M := S.topologicalClosure
      have hConv : Convex ℝ (M : Set E) := (M.restrictScalars ℝ).convex
      obtain ⟨φ, c, hBound, hStrict⟩ := RCLike.geometric_hahn_banach_closed_point
        (𝕜 := ℂ) hConv S.isClosed_topologicalClosure (hx i)
      have hPos : 0 < c := by simpa using hBound 0 M.zero_mem
      have hRe (y : E) (hy : y ∈ M) : (φ y).re = 0 := by
        by_contra hne
        let a : ℝ := (c + 1) / (φ y).re
        have h := hBound ((a : ℂ) • y) (M.smul_mem _ hy)
        change (φ ((a : ℂ) • y)).re < c at h
        rw [map_smul, smul_eq_mul, Complex.mul_re]
          at h
        simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
        change (c + 1) / (φ y).re * (φ y).re < c at h
        rw [div_mul_cancel₀ _ hne] at h
        linarith
      have hZero (y : E) (hy : y ∈ M) : φ y = 0 := by
        apply Complex.ext (hRe y hy)
        have h := hRe (Complex.I • y) (M.smul_mem _ hy)
        rwa [map_smul, smul_eq_mul, Complex.mul_re, Complex.I_re, Complex.I_im,
          zero_mul, one_mul, zero_sub, neg_eq_zero] at h
      have hne : φ (x i) ≠ 0 := by
        intro h
        rw [h] at hStrict
        exact (hPos.trans hStrict).false
      refine ⟨(φ (x i))⁻¹ • φ, ?_, fun j hij => ?_⟩
      · change (φ (x i))⁻¹ * φ (x i) = 1
        exact inv_mul_cancel₀ hne
      · have hj : x j ∈ M := S.le_topologicalClosure
          (Submodule.subset_span ⟨j, Ne.symm hij, rfl⟩)
        change (φ (x i))⁻¹ * φ (x j) = 0
        rw [hZero _ hj, mul_zero]
    choose u hOne hZero using hSeparate
    exact ⟨u, hOne, hZero⟩
  · rintro ⟨u, hOne, hZero⟩ i hi
    let S := Submodule.span ℂ (x '' {j : ι | j ≠ i})
    have hLe : S ≤ (u i).ker := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨j, hj, rfl⟩
      exact hZero i j (Ne.symm hj)
    have hIn : x i ∈ (u i).ker := closure_minimal hLe (u i).isClosed_ker hi
    change u i (x i) = 0 at hIn
    exact one_ne_zero ((hOne i).symm.trans hIn)
