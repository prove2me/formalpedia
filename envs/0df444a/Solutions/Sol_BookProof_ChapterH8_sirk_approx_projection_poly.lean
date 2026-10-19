-- Prove2me | solution 1 for BookProof.ChapterH8.sirk_approx_projection_poly
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:59:04.415466+00:00
-- url     : https://prove2.me/submissions/6b73c5b2-ca44-4cd6-9eb6-07b615c84d1a

import Definitions.Def_ChapterH5
import Definitions.Def_ChapterH6
import Mathlib
import Definitions.Def_ChapterH8
import Definitions.Def_ChapterH4
-- Generated from ChapterH8.lean — theorem BookProof.ChapterH8.sirk_approx_projection_poly
open BookProof.ChapterH4
open BookProof.ChapterH8


noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6
open ContinuousLinearMap

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem solution (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G)
    (X : E →L[ℂ] E) (hJ : Vn = Vm.comp J)
    (hVm : (adjoint Vm).comp Vm = ContinuousLinearMap.id ℂ G)
    (hJJ : (adjoint J).comp J = ContinuousLinearMap.id ℂ F)
    (hinvadj : ∀ x : F, ∃ y : F, (adjoint X) (Vn x) = Vn y)
    (p : Polynomial ℂ) (v : E) :
    Vn ((adjoint Vn) (Vm ((Polynomial.aeval (compress Vm X) p) ((adjoint Vm) v))))
      = Vn ((Polynomial.aeval (compress Vn X) p) ((adjoint Vn) v)) := by
  set A := compress Vm X with hA
  set B := compress Vn X with hB
  have hJ' : adjoint Vn = (adjoint J).comp (adjoint Vm) := by rw [hJ, adjoint_comp]
  -- (a) B = J† A J
  have hBA : B = (adjoint J).comp (A.comp J) := by
    rw [hB, hA, compress, compress, hJ', hJ]; rfl
  -- (b) invariance of range J under A†
  have hinv : ∀ x : F, (adjoint A) (J x) = J ((adjoint J) ((adjoint A) (J x))) := by
    intro x
    obtain ⟨y, hy⟩ := hinvadj x
    have hAadj : adjoint A = (adjoint Vm).comp ((adjoint X).comp Vm) := by
      rw [hA, compress, adjoint_comp, adjoint_comp, adjoint_adjoint, ContinuousLinearMap.comp_assoc]
    have h1 : (adjoint A) (J x) = J y := by
      rw [hAadj]
      simp only [ContinuousLinearMap.comp_apply]
      have : Vm (J x) = Vn x := by rw [hJ]; rfl
      rw [this, hy, hJ]
      simp only [ContinuousLinearMap.comp_apply]
      have := congrArg (fun T : G →L[ℂ] G => T (J y)) hVm
      simpa using this
    rw [h1]
    have := congrArg (fun T : F →L[ℂ] F => T y) hJJ
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this
    rw [this]
  have hJJx : ∀ z : F, (adjoint J) (J z) = z := fun z => by
    have := congrArg (fun T : F →L[ℂ] F => T z) hJJ
    simpa using this
  have hVmx : ∀ z : G, (adjoint Vm) (Vm z) = z := fun z => by
    have := congrArg (fun T : G →L[ℂ] G => T z) hVm
    simpa using this
  -- (c),(d): J† A Q = J† A where Q = J J†
  have hd : ∀ g : G, (adjoint J) (A (J ((adjoint J) g))) = (adjoint J) (A g) := by
    intro g
    apply ext_inner_left ℂ
    intro f
    set z := (adjoint J) ((adjoint A) (J f)) with hz
    calc inner ℂ f ((adjoint J) (A (J ((adjoint J) g))))
        = inner ℂ (J f) (A (J ((adjoint J) g))) := adjoint_inner_right _ _ _
      _ = inner ℂ ((adjoint A) (J f)) (J ((adjoint J) g)) := (adjoint_inner_left _ _ _).symm
      _ = inner ℂ (J z) (J ((adjoint J) g)) := by rw [← hinv f]
      _ = inner ℂ ((adjoint J) (J z)) ((adjoint J) g) := (adjoint_inner_left _ _ _).symm
      _ = inner ℂ z ((adjoint J) g) := by rw [hJJx]
      _ = inner ℂ (J z) g := adjoint_inner_right _ _ _
      _ = inner ℂ ((adjoint A) (J f)) g := by rw [← hinv f]
      _ = inner ℂ (J f) (A g) := adjoint_inner_left _ _ _
      _ = inner ℂ f ((adjoint J) (A g)) := (adjoint_inner_right _ _ _).symm
  -- (e) B^k J† = J† A^k
  have hpow : ∀ k : ℕ, ∀ g : G, (B ^ k) ((adjoint J) g) = (adjoint J) ((A ^ k) g) := by
    intro k
    induction k with
    | zero => intro g; simp
    | succ k ih =>
      intro g
      rw [pow_succ', pow_succ', ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, ih, hBA]
      simp only [ContinuousLinearMap.comp_apply]
      rw [hd]
  have hpoly : ∀ g : G, (Polynomial.aeval B p) ((adjoint J) g) =
      (adjoint J) ((Polynomial.aeval A p) g) := by
    intro g
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add, ContinuousLinearMap.add_apply, hp, hq]
    | monomial n a =>
      simp only [Polynomial.aeval_monomial, ContinuousLinearMap.mul_apply, map_smul,
        Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, hpow]
  -- (f) assemble
  rw [hJ', hJ]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hVmx, ← hpoly]
