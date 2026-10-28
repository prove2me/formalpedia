-- Prove2me | solution 1 for CountingMatroid.Analysis.ConnectedNormalizedRayleigh.connected_normalized_rayleigh
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:53:05.279504+00:00
-- url     : https://prove2.me/submissions/6c92839d-e36b-4642-a972-c57217e580d6

import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Tactic
import Theorems.Thm_CountingMatroid_Analysis_ConnectedLaplacianKernel_connected_laplacian_kernel
import Theorems.Thm_CountingMatroid_Analysis_ConnectedLaplacianKernel_laplacian_energy
import Theorems.Thm_CountingMatroid_Analysis_RayleighFixedKernel_rayleigh_fixed_kernel

namespace CountingMatroid.Analysis.ConnectedNormalizedRayleigh
end CountingMatroid.Analysis.ConnectedNormalizedRayleigh
namespace CountingMatroid.Analysis.ConnectedLaplacianKernel
end CountingMatroid.Analysis.ConnectedLaplacianKernel
namespace CountingMatroid.Analysis.RayleighFixedKernel
end CountingMatroid.Analysis.RayleighFixedKernel
set_option autoImplicit false

namespace CountingMatroid.Analysis.ConnectedNormalizedRayleigh
end CountingMatroid.Analysis.ConnectedNormalizedRayleigh
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ConnectedNormalizedRayleigh

open scoped BigOperators ComplexOrder
open QuadraticNonpositiveHyperplane

/-- INTERNAL: Row normalization realizes the connected Rayleigh argument in
 a positive weighted inner product, assigning weight one to zero rows. -/
theorem solution {σ : Type} [Fintype σ] [DecidableEq σ]
    (C : Matrix σ σ ℝ) (hC : ∀ i j, 0 ≤ C i j)
    (hsym : ∀ i j, C i j = C j i)
    (hcross : ∀ U : Set σ,
      (∃ i j, C i j ≠ 0 ∧ i ∈ U) →
      (∃ i j, C i j ≠ 0 ∧ i ∉ U) →
      ∃ i j, C i j ≠ 0 ∧ i ∈ U ∧ j ∉ U)
    (hbound : ∀ v : σ → ℝ, (∑ i, v i * C.mulVec v i) ≤
      ∑ i, (C.mulVec v i)^2 / (∑ j, C i j)) :
    HasNonpositiveHyperplane C.toQuadraticForm' := by
  classical
  let r : σ → ℝ := fun i => ∑ j, C i j
  let d : σ → ℝ := fun i => if r i = 0 then 1 else r i
  have hr (i : σ) : 0 ≤ r i := Finset.sum_nonneg (fun j _ => hC i j)
  have hd (i : σ) : 0 < d i := by
    dsimp [d]
    split_ifs with h
    · norm_num
    · exact lt_of_le_of_ne (hr i) (Ne.symm h)
  have hrow (i : σ) (hi : r i = 0) (j : σ) : C i j = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hC i j)).mp hi j (Finset.mem_univ j)
  have hmulzero (i : σ) (hi : r i = 0) (v : σ → ℝ) : C.mulVec v i = 0 := by
    simp [Matrix.mulVec, dotProduct, hrow i hi]
  let D := Matrix.diagonal d
  have hD : D.PosDef := Matrix.posDef_diagonal_iff.mpr hd
  letI := D.toNormedAddCommGroup hD
  letI := D.toSeminormedAddCommGroup hD.posSemidef
  letI := D.toInnerProductSpace hD.posSemidef
  have hinner (u v : σ → ℝ) : inner ℝ u v = ∑ i, d i * u i * v i := by
    change (D.mulVec v) ⬝ᵥ star u = _
    simp only [D, Matrix.mulVec_diagonal, star_trivial, dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    ring
  let T : (σ → ℝ) →ₗ[ℝ] (σ → ℝ) :=
    { toFun := fun v i => C.mulVec v i / d i
      map_add' := by intro u v; ext i; simp [Matrix.mulVec_add, add_div]
      map_smul' := by intro a v; ext i; simp [Matrix.mulVec_smul, mul_div_assoc] }
  have hT (v : σ → ℝ) (i : σ) : T v i = C.mulVec v i / d i := rfl
  have hq (u v : σ → ℝ) : inner ℝ u (T v) = ∑ i, u i * C.mulVec v i := by
    rw [hinner]
    apply Finset.sum_congr rfl
    intro i _
    rw [hT]
    field_simp [(hd i).ne']
  have hsymT : LinearMap.IsSymmetric (𝕜 := ℝ) (E := σ → ℝ) T := by
    intro u v
    rw [real_inner_comm v (T u), hq, hq]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym j i]
    ring
  let l : (σ → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun v => ∑ i, r i * v i
      map_add' := by intro u v; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by intro a v; simp [← Finset.mul_sum, mul_left_comm] }
  have hl (v : σ → ℝ) : l v = ∑ i, r i * v i := rfl
  have hrd (i : σ) (v : σ → ℝ) : r i * T v i = C.mulVec v i := by
    by_cases hi : r i = 0
    · rw [hi, zero_mul, hmulzero i hi]
    · rw [hT]
      dsimp [d]
      rw [if_neg hi]
      field_simp
  have hinv (v : σ → ℝ) : l (T v) = l v := by
    simp only [hl, hrd, Matrix.mulVec, dotProduct, r, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym j i]
  have hupper (v : σ → ℝ) : inner ℝ v (T v) ≤ inner ℝ v v := by
    rw [hq, hinner]
    have he := ConnectedLaplacianKernel.laplacian_energy C hsym v
    have hn : 0 ≤ ∑ i, ∑ j, C i j * (v i - v j)^2 :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
        mul_nonneg (hC i j) (sq_nonneg _)))
    have hh : (∑ i, r i * (v i)^2) ≤ ∑ i, d i * v i * v i := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : r i = 0
      · simp [d, hi, mul_self_nonneg]
      · simp only [d, if_neg hi]
        nlinarith
    change (∑ i, r i * (v i)^2) - _ = _ at he
    linarith
  have hsq (v : σ → ℝ) : inner ℝ (T v) (T v) =
      ∑ i, (C.mulVec v i)^2 / r i := by
    rw [hinner]
    apply Finset.sum_congr rfl
    intro i _
    rw [hT]
    by_cases hi : r i = 0
    · simp [hmulzero i hi v, hi]
    · simp only [d, if_neg hi]
      field_simp
  have hb (v : σ → ℝ) : inner ℝ v (T v) ≤ inner ℝ (T v) (T v) := by
    rw [hq, hsq]
    exact hbound v
  have hf (v : σ → ℝ) (hv : T v = v) (hm : l v = 0) : v = 0 := by
    have hbal (i : σ) : C.mulVec v i = r i * v i := by
      simpa only [hv] using (hrd i v).symm
    have hz := ConnectedLaplacianKernel.connected_laplacian_kernel C hC hsym hcross v
      hbal hm
    have ht : T v = 0 := by ext i; simp [hT, hz]
    exact hv.symm.trans ht
  refine ⟨l, ?_⟩
  intro v hv
  have hh := RayleighFixedKernel.rayleigh_fixed_kernel T hsymT l hinv hupper hb hf v hv
  rw [hq] at hh
  simpa [Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply', dotProduct] using hh
