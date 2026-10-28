-- Prove2me | solution 1 for CountingMatroid.Analysis.ConnectedRayleighHyperplane.connected_rayleigh_hyperplane
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:54:07.406755+00:00
-- url     : https://prove2.me/submissions/1afa6731-5061-4797-b78e-2b30d9ca68d9

import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Tactic
import Theorems.Thm_CountingMatroid_Analysis_ConnectedNormalizedRayleigh_connected_normalized_rayleigh

namespace CountingMatroid.Analysis.ConnectedRayleighHyperplane
end CountingMatroid.Analysis.ConnectedRayleighHyperplane
namespace CountingMatroid.Analysis.ConnectedNormalizedRayleigh
end CountingMatroid.Analysis.ConnectedNormalizedRayleigh
namespace CountingMatroid.Analysis.ConnectedLaplacianKernel
end CountingMatroid.Analysis.ConnectedLaplacianKernel
namespace CountingMatroid.Analysis.RayleighFixedKernel
end CountingMatroid.Analysis.RayleighFixedKernel
namespace CountingMatroid.Analysis.QuadraticSignatureHyperplane
end CountingMatroid.Analysis.QuadraticSignatureHyperplane
section


set_option autoImplicit false

/-!
A quadratic form is nonpositive on a hyperplane if some real linear
functional has a nonpositive kernel. This property survives linear pullback
and nonnegative scaling. It implies the signature bound, and also gives
nonpositivity on the orthogonal complement of any positive vector.
No property of matroid polynomials is assumed or asserted here.
-/

namespace CountingMatroid.Analysis.QuadraticNonpositiveHyperplane



/-- INTERNAL: Pulling back a nonpositive hyperplane needs no injectivity,
surjectivity, or sign conditions on the linear map.
TEXLINE: main.tex:326-348 -/
theorem HasNonpositiveHyperplane.comp {V W : Type}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {Q : QuadraticForm ℝ V} (hQ : HasNonpositiveHyperplane Q) (A : W →ₗ[ℝ] V) :
    HasNonpositiveHyperplane (Q.comp A) := by
  obtain ⟨l, hl⟩ := hQ
  exact ⟨l.comp A, fun v hv => hl (A v) hv⟩







end CountingMatroid.Analysis.QuadraticNonpositiveHyperplane

end
set_option autoImplicit false

/-!
A matrix formulation of the spectral step in cubic contraction. The weighted
Rayleigh inequality excludes normalized eigenvalues strictly between zero and
one. Connected nonnegative support must then make the eigenvalue one simple.
Zero rows are handled by assigning them unit weight in the auxiliary inner
product; the resulting hyperplane is transported by positive diagonal scaling.
-/

namespace CountingMatroid.Analysis.ConnectedRayleighHyperplane
end CountingMatroid.Analysis.ConnectedRayleighHyperplane
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ConnectedRayleighHyperplane

open scoped BigOperators
open QuadraticNonpositiveHyperplane

/-- INTERNAL: The tensor-free spectral bridge. Zero rows are allowed; cuts
need only connect coordinates incident to a nonzero matrix entry.
TEXLINE: main.tex:340-347 -/
theorem solution {σ : Type} [Fintype σ] [DecidableEq σ]
    [Invertible (2 : ℝ)] (A : Matrix σ σ ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hsym : ∀ i j, A i j = A j i)
    (hcross : ∀ U : Set σ,
      (∃ i j, A i j ≠ 0 ∧ i ∈ U) →
      (∃ i j, A i j ≠ 0 ∧ i ∉ U) →
      ∃ i j, A i j ≠ 0 ∧ i ∈ U ∧ j ∉ U)
    (w : σ → ℝ) (hw : ∀ i, 0 < w i)
    (hbound : ∀ v : σ → ℝ, Matrix.toQuadraticForm' A v ≤
      ∑ i, w i * (A.mulVec v i) ^ 2 / A.mulVec w i) :
    HasNonpositiveHyperplane (Matrix.toQuadraticForm' A) := by
  classical
  by_cases hz : A = 0
  · subst A
    refine ⟨0, ?_⟩
    intro v _
    simp [Matrix.toQuadraticForm']
  let C : Matrix σ σ ℝ := fun i j => w i * A i j * w j
  have hC : ∀ i j, 0 ≤ C i j := fun i j =>
    mul_nonneg (mul_nonneg (hw i).le (hA i j)) (hw j).le
  have hCsym : ∀ i j, C i j = C j i := by
    intro i j
    dsimp [C]
    rw [hsym i j]
    ring
  have hsupport (i j : σ) : C i j ≠ 0 ↔ A i j ≠ 0 := by
    simp only [C, ne_eq, mul_eq_zero, (hw i).ne', (hw j).ne', false_or, or_false]
  have hCcross : ∀ U : Set σ,
      (∃ i j, C i j ≠ 0 ∧ i ∈ U) →
      (∃ i j, C i j ≠ 0 ∧ i ∉ U) →
      ∃ i j, C i j ≠ 0 ∧ i ∈ U ∧ j ∉ U := by
    intro U hin hout
    obtain ⟨i, j, hij, hi, hj⟩ := hcross U
      (by simpa only [hsupport] using hin) (by simpa only [hsupport] using hout)
    exact ⟨i, j, (hsupport i j).mpr hij, hi, hj⟩
  have hmul (x : σ → ℝ) (i : σ) :
      C.mulVec x i = w i * A.mulVec (fun j => w j * x j) i := by
    simp only [Matrix.mulVec, dotProduct, C, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hrow (i : σ) : (∑ j, C i j) = w i * A.mulVec w i := by
    simp only [Matrix.mulVec, dotProduct, C, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hquad (x : σ → ℝ) : (∑ i, x i * C.mulVec x i) =
      A.toQuadraticForm' (fun i => w i * x i) := by
    simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply', dotProduct, hmul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hCbound (x : σ → ℝ) : (∑ i, x i * C.mulVec x i) ≤
      ∑ i, (C.mulVec x i)^2 / (∑ j, C i j) := by
    rw [hquad]
    refine (hbound (fun i => w i * x i)).trans_eq ?_
    apply Finset.sum_congr rfl
    intro i _
    rw [hmul, hrow]
    by_cases hi : A.mulVec w i = 0
    · simp [hi]
    · field_simp [(hw i).ne', hi]
  have hCQ := ConnectedNormalizedRayleigh.connected_normalized_rayleigh C hC hCsym
    hCcross hCbound
  let S : (σ → ℝ) →ₗ[ℝ] (σ → ℝ) :=
    { toFun := fun v i => v i / w i
      map_add' := by intro u v; ext i; simp [add_div]
      map_smul' := by intro c v; ext i; simp [mul_div_assoc] }
  have hforms : C.toQuadraticForm'.comp S = A.toQuadraticForm' := by
    ext v
    change C.toQuadraticForm' (S v) = A.toQuadraticForm' v
    have hv : (fun i => w i * S v i) = v := by
      ext i
      change w i * (v i / w i) = v i
      field_simp [(hw i).ne']
    have hh := hquad (S v)
    rw [hv] at hh
    simpa [Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply', dotProduct] using hh
  rw [← hforms]
  exact hCQ.comp S
