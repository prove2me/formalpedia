-- Prove2me | solution 1 for BookProof.ChapterH8.sirk_band_refinement_of_orthonormal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:00:02.01285+00:00
-- url     : https://prove2.me/submissions/7ed6a9c8-95df-4eb2-b9ef-f2da76df337d

import Definitions.Def_ChapterH5
import Definitions.Def_ChapterH6
import Mathlib
import Definitions.Def_ChapterH8Bases
import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH8
-- Generated from ChapterH8Bases.lean — theorem BookProof.ChapterH8.sirk_band_refinement_of_orthonormal
open BookProof.ChapterH4
open BookProof.ChapterH8


noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

open ContinuousLinearMap
theorem iso_poly_aux {F E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (V : F →L[ℂ] E) (hV : ∀ x y, inner ℂ (V x) (V y) = inner ℂ x y) (X : E →L[ℂ] E)
    (hinv : ∀ x, ∃ y, X (V x) = V y) (p : Polynomial ℂ) (v : E)
    (hv : V ((adjoint V) v) = v) :
    V ((Polynomial.aeval (compress V X) p) ((adjoint V) v)) = (Polynomial.aeval X p) v := by
  have hVV : ∀ z, (adjoint V) (V z) = z := by
    intro z
    apply ext_inner_left ℂ
    intro f
    rw [adjoint_inner_right, hV]
  have hXV : ∀ x, X (V x) = V ((compress V X) x) := by
    intro x
    obtain ⟨y, hy⟩ := hinv x
    simp only [compress, ContinuousLinearMap.comp_apply, hy, hVV]
  have hpow : ∀ k : ℕ, ∀ x, (X ^ k) (V x) = V (((compress V X) ^ k) x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, pow_succ, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hXV, ih]
  have hpoly : ∀ x, (Polynomial.aeval X p) (V x) = V ((Polynomial.aeval (compress V X) p) x) := by
    intro x
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add, ContinuousLinearMap.add_apply, hp, hq]
    | monomial n a =>
      simp only [Polynomial.aeval_monomial, ContinuousLinearMap.mul_apply, map_smul,
        Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, hpow]
  rw [← hpoly, hv]

theorem nested_aux {m n : ℕ} (hmn : m ≤ n)
    (w : Fin m → E) (w' : Fin n → E) (hw : Orthonormal ℂ w) (hw' : Orthonormal ℂ w')
    (hnest : ∀ i : Fin m, w i = w' (Fin.castLE hmn i)) :
    orthonormalEmbedding w hw = (orthonormalEmbedding w' hw').comp (coordIncl hmn) := by
  have hbasis : ∀ {k : ℕ} (u : Fin k → E) (hu : Orthonormal ℂ u) (i : Fin k),
      orthonormalEmbedding u hu (EuclideanSpace.single i (1 : ℂ)) = u i := by
    intro k u hu i
    have : (EuclideanSpace.single i (1 : ℂ)) = (EuclideanSpace.basisFun (Fin k) ℂ).toBasis i := by
      simp
    rw [this]
    show ((EuclideanSpace.basisFun (Fin k) ℂ).toBasis.constr ℂ u) _ = u i
    exact Module.Basis.constr_basis _ _ _ _
  have hbasis2 : ∀ (u : Fin m → EuclideanSpace ℂ (Fin n)) (hu : Orthonormal ℂ u) (i : Fin m),
      orthonormalEmbedding u hu (EuclideanSpace.single i (1 : ℂ)) = u i := by
    intro u hu i
    have : (EuclideanSpace.single i (1 : ℂ)) = (EuclideanSpace.basisFun (Fin m) ℂ).toBasis i := by
      simp
    rw [this]
    show ((EuclideanSpace.basisFun (Fin m) ℂ).toBasis.constr ℂ u) _ = u i
    exact Module.Basis.constr_basis _ _ _ _
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin m) ℂ).toBasis.ext
  intro i
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply]
  rw [hbasis, coordIncl, hbasis2, hbasis, hnest]


theorem solution {m n : ℕ} (hmn : m ≤ n) (X : E →L[ℂ] E)
    (w : Fin m → E) (w' : Fin n → E) (hw : Orthonormal ℂ w) (hw' : Orthonormal ℂ w')
    (hnest : ∀ i : Fin m, w i = w' (Fin.castLE hmn i))
    (hinvm : ∀ x, ∃ y, X (orthonormalEmbedding w hw x) = orthonormalEmbedding w hw y)
    (hinvn : ∀ x, ∃ y, X (orthonormalEmbedding w' hw' x) = orthonormalEmbedding w' hw' y)
    (p : Polynomial ℂ) (v : E)
    (hv : orthonormalEmbedding w hw ((adjoint (orthonormalEmbedding w hw)) v) = v) :
    orthonormalEmbedding w' hw'
        ((Polynomial.aeval (compress (orthonormalEmbedding w' hw') X) p)
          ((adjoint (orthonormalEmbedding w' hw')) v))
      = orthonormalEmbedding w hw
        ((Polynomial.aeval (compress (orthonormalEmbedding w hw) X) p)
          ((adjoint (orthonormalEmbedding w hw)) v)) := by
  have hiso : ∀ {k : ℕ} (u : Fin k → E) (hu : Orthonormal ℂ u) (x y : EuclideanSpace ℂ (Fin k)),
      inner ℂ (orthonormalEmbedding u hu x) (orthonormalEmbedding u hu y) = inner ℂ x y := by
    intro k u hu x y
    exact (orthonormalEmbeddingLI u hu).inner_map_map x y
  rw [iso_poly_aux _ (hiso w hw) X hinvm p v hv]
  have hv' : orthonormalEmbedding w' hw' ((adjoint (orthonormalEmbedding w' hw')) v) = v := by
    have hVV : ∀ z, (adjoint (orthonormalEmbedding w' hw')) (orthonormalEmbedding w' hw' z) = z := by
      intro z
      apply ext_inner_left ℂ
      intro f
      rw [adjoint_inner_right, hiso]
    rw [← hv, nested_aux hmn w w' hw hw' hnest, ContinuousLinearMap.comp_apply, hVV]
  exact iso_poly_aux _ (hiso w' hw') X hinvn p v hv'
