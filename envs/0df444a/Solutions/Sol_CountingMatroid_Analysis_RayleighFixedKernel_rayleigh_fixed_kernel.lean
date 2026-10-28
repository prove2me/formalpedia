-- Prove2me | solution 1 for CountingMatroid.Analysis.RayleighFixedKernel.rayleigh_fixed_kernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:47:02.415765+00:00
-- url     : https://prove2.me/submissions/b31d7899-6ed1-4805-b0e8-79f9d50b6760

import Mathlib.Analysis.InnerProductSpace.Spectrum

namespace CountingMatroid.Analysis.RayleighFixedKernel
end CountingMatroid.Analysis.RayleighFixedKernel
set_option autoImplicit false

namespace CountingMatroid.Analysis.RayleighFixedKernel
end CountingMatroid.Analysis.RayleighFixedKernel
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RayleighFixedKernel

open scoped BigOperators

/-- INTERNAL: Spectral exclusion on an invariant kernel. The two Rayleigh
bounds exclude eigenvalues in `(0,1)`, and the fixed-vector condition excludes
one on the kernel. -/
theorem solution {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (l : E →ₗ[ℝ] ℝ)
    (hinv : ∀ v, l (T v) = l v)
    (hupper : ∀ v, inner ℝ v (T v) ≤ inner ℝ v v)
    (hbound : ∀ v, inner ℝ v (T v) ≤ inner ℝ (T v) (T v))
    (hfixed : ∀ v, T v = v → l v = 0 → v = 0) :
    ∀ v, l v = 0 → inner ℝ v (T v) ≤ 0 := by
  let K := LinearMap.ker l
  have hinvariant : ∀ v ∈ K, T v ∈ K := by
    intro v hv
    change l (T v) = 0
    rw [hinv]
    exact hv
  let S := T.restrict hinvariant
  have hS : S.IsSymmetric := hT.restrict_invariant hinvariant
  let b := hS.eigenvectorBasis rfl
  have heig (i : Fin (Module.finrank ℝ K)) : hS.eigenvalues rfl i ≤ 0 := by
    let x := b i
    let a := hS.eigenvalues rfl i
    have hx : x ≠ 0 := b.orthonormal.ne_zero i
    have he : S x = a • x := hS.apply_eigenvectorBasis rfl i
    have he' : T (x : E) = a • (x : E) := congrArg Subtype.val he
    have hnorm : 0 < inner ℝ (x : E) (x : E) := by
      exact real_inner_self_pos.mpr (by simpa using hx)
    have hu := hupper (x : E)
    have hb := hbound (x : E)
    rw [he', inner_smul_right] at hu
    rw [he', inner_smul_right, inner_smul_left, inner_smul_right] at hb
    simp only [conj_trivial] at hb
    have hau : a ≤ 1 := by nlinarith
    by_contra ha
    have hap : 0 < a := lt_of_not_ge ha
    have hae : a = 1 := by
      have hprod : 0 < a * inner ℝ (x : E) (x : E) := mul_pos hap hnorm
      have hlow : 1 ≤ a := by
        have : a * inner ℝ (x : E) (x : E) ≤
            a * (a * inner ℝ (x : E) (x : E)) := hb
        have hh : (1 : ℝ) * (a * inner ℝ (x : E) (x : E)) ≤
            a * (a * inner ℝ (x : E) (x : E)) := by simpa using this
        exact (mul_le_mul_iff_left₀ hprod).mp hh
      exact le_antisymm hau hlow
    have hz := hfixed (x : E) (by simpa [hae] using he') x.property
    exact hx (Subtype.ext hz)
  intro v hv
  let x : K := ⟨v, hv⟩
  change inner ℝ x (S x) ≤ 0
  rw [← b.sum_inner_mul_inner x (S x)]
  apply Finset.sum_nonpos
  intro i _
  have he := hS.apply_eigenvectorBasis rfl i
  have hs : inner ℝ (b i) (S x) = hS.eigenvalues rfl i * inner ℝ (b i) x := by
    rw [← hS, he, inner_smul_left]
    simp only [conj_trivial]
    rfl
  rw [hs, real_inner_comm x (b i)]
  have := mul_nonpos_of_nonpos_of_nonneg (heig i) (sq_nonneg (inner ℝ (b i) x))
  convert this using 1 <;> rw [real_inner_comm x (b i)] <;> ring
