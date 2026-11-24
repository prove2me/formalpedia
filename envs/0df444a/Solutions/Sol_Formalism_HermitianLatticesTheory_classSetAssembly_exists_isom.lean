-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.classSetAssembly_exists_isom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:43:19.699871+00:00
-- url     : https://prove2.me/submissions/432ee753-0f90-469c-9428-130696aed3c8

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetAssembly
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_tr_add_left
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_tr_sub_left
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_tr_qsmul_left
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_tr_qsmul_right
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_tr_sum_left
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_tr_sum_right
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_nondeg
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_span
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module Matrix
noncomputable section
namespace Formalism.HermitianLatticesTheory
section Trace
variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
end Trace
section Real
variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
end Real
section Finite
variable {V : Type*} [AddCommGroup V]
end Finite
section Isom
variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
private theorem eq_of_trace_apply_eq_lemma_5 {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (ι : V →+ EuclideanSpace ℝ (Fin n))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (w : Fin n → V) (hw : LinearIndependent ℝ (ι ∘ w)) (y y' : V)
    (hyy : ∀ l, Algebra.trace ℚ K (h y (w l)) = Algebra.trace ℚ K (h y' (w l))) : y = y' := by
  have hz : y - y' = 0 := classSetAssembly_nondeg h hpos ι hι w hw _ (fun l => by
    rw [classSetAssembly_tr_sub_left, hyy l, sub_self])
  exact sub_eq_zero.mp hz
private theorem trace_sum_coeffs_lemma_6 {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K) (t : Fin n → ℚ)
    (w : Fin n → V) (z : V) :
    Algebra.trace ℚ K (h (∑ i, (t i : K) • w i) z) =
      ∑ i, t i * Algebra.trace ℚ K (h (w i) z) := by
  rw [classSetAssembly_tr_sum_left]
  exact Finset.sum_congr rfl fun i _ => classSetAssembly_tr_qsmul_left h _ _ _
private theorem trace_smul_sum_coeffs_lemma_7 {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K) (a : K) (t : Fin n → ℚ)
    (w : Fin n → V) (z : V) :
    Algebra.trace ℚ K (h (a • ∑ i, (t i : K) • w i) z) =
      ∑ i, t i * Algebra.trace ℚ K (h (a • w i) z) := by
  rw [Finset.smul_sum, classSetAssembly_tr_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, mul_comm a, ← smul_smul, classSetAssembly_tr_qsmul_left]
private theorem trace_smul_left_basis_lemma_8 {κ : Type*} [Fintype κ] (ω : Basis κ ℚ K)
    (h : V →ₗ⋆[K] V →ₗ[K] K) (a : K) (y z : V) :
    Algebra.trace ℚ K (h (a • y) z) =
      ∑ k, ω.repr a k * Algebra.trace ℚ K (h (ω k • y) z) := by
  have ha : a = ∑ k, ((ω.repr a k : ℚ) : K) * ω k := by
    conv_lhs => rw [← ω.sum_repr a]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, eq_ratCast]
  conv_lhs => rw [ha]
  rw [Finset.sum_smul, classSetAssembly_tr_sum_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul, classSetAssembly_tr_qsmul_left]
private theorem exists_linearMap_of_gram_lemma_9 {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (ι : V →+ EuclideanSpace ℝ (Fin n))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    {κ : Type*} [Fintype κ] (ω : Basis κ ℚ K)
    (u u' : Fin n → V) (hu : LinearIndependent ℝ (ι ∘ u)) (hu' : LinearIndependent ℝ (ι ∘ u'))
    (hG : ∀ i l, Algebra.trace ℚ K (h (u i) (u l)) = Algebra.trace ℚ K (h (u' i) (u' l)))
    (hA : ∀ k i l, Algebra.trace ℚ K (h (ω k • u i) (u l)) =
      Algebra.trace ℚ K (h (ω k • u' i) (u' l))) :
    ∃ φ : V →ₗ[K] V, ∀ x l,
      Algebra.trace ℚ K (h (φ x) (u' l)) = Algebra.trace ℚ K (h x (u l)) := by
  choose t ht using classSetAssembly_span h hpos ι hι u hu
  have hP : ∀ x l, Algebra.trace ℚ K (h (∑ i, (t x i : K) • u' i) (u' l)) =
      Algebra.trace ℚ K (h x (u l)) := by
    intro x l
    conv_rhs => rw [ht x]
    rw [trace_sum_coeffs_lemma_6, trace_sum_coeffs_lemma_6]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hG i l]
  have hQ : ∀ (k : κ) x l, Algebra.trace ℚ K (h (ω k • ∑ i, (t x i : K) • u' i) (u' l)) =
      Algebra.trace ℚ K (h (ω k • x) (u l)) := by
    intro k x l
    conv_rhs => rw [ht x]
    rw [trace_smul_sum_coeffs_lemma_7, trace_smul_sum_coeffs_lemma_7]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hA k i l]
  obtain ⟨f, hf⟩ : ∃ f : V → V, ∀ x l,
      Algebra.trace ℚ K (h (f x) (u' l)) = Algebra.trace ℚ K (h x (u l)) ∧
      ∀ k, Algebra.trace ℚ K (h (ω k • f x) (u' l)) = Algebra.trace ℚ K (h (ω k • x) (u l)) :=
    ⟨fun x => ∑ i, (t x i : K) • u' i, fun x l => ⟨hP x l, fun k => hQ k x l⟩⟩
  refine ⟨{ toFun := f
            map_add' := fun x y => eq_of_trace_apply_eq_lemma_5 h hpos ι hι u' hu' _ _ (fun l => by
              rw [classSetAssembly_tr_add_left, (hf (x + y) l).1, (hf x l).1, (hf y l).1,
                classSetAssembly_tr_add_left])
            map_smul' := fun a x => eq_of_trace_apply_eq_lemma_5 h hpos ι hι u' hu' _ _ (fun l => by
              rw [(hf (a • x) l).1]
              try rw [RingHom.id_apply]
              rw [trace_smul_left_basis_lemma_8 ω h a x (u l), trace_smul_left_basis_lemma_8 ω h a (f x) (u' l)]
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [(hf x l).2 k]) }, fun x l => (hf x l).1⟩
end Isom
section Main
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
end Main
end Formalism.HermitianLatticesTheory
end
end

set_option autoImplicit false
open Module Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (ι : V →+ EuclideanSpace ℝ (Fin n))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    {κ : Type*} [Fintype κ] (ω : Basis κ ℚ K)
    (u u' : Fin n → V) (hu : LinearIndependent ℝ (ι ∘ u)) (hu' : LinearIndependent ℝ (ι ∘ u'))
    (hG : ∀ i l, Algebra.trace ℚ K (h (u i) (u l)) = Algebra.trace ℚ K (h (u' i) (u' l)))
    (hA : ∀ k i l, Algebra.trace ℚ K (h (ω k • u i) (u l)) =
      Algebra.trace ℚ K (h (ω k • u' i) (u' l))) :
    ∃ φ : V ≃ₗ[K] V, (∀ x y, Algebra.trace ℚ K (h (φ x) (φ y)) = Algebra.trace ℚ K (h x y)) ∧
      ∀ i, φ (u i) = u' i := by
  obtain ⟨φ, hφ⟩ := exists_linearMap_of_gram_lemma_9 h hpos ι hι ω u u' hu hu' hG hA
  obtain ⟨ψ, hψ⟩ := exists_linearMap_of_gram_lemma_9 h hpos ι hι ω u' u hu' hu
    (fun i l => (hG i l).symm) (fun k i l => (hA k i l).symm)
  have h1 : ∀ y, φ (ψ y) = y := fun y =>
    eq_of_trace_apply_eq_lemma_5 h hpos ι hι u' hu' _ _ (fun l => by rw [hφ, hψ])
  have h2 : ∀ x, ψ (φ x) = x := fun x =>
    eq_of_trace_apply_eq_lemma_5 h hpos ι hι u hu _ _ (fun l => by rw [hψ, hφ])
  have hφu : ∀ i, φ (u i) = u' i := fun i =>
    eq_of_trace_apply_eq_lemma_5 h hpos ι hι u' hu' _ _ (fun l => by rw [hφ, hG i l])
  refine ⟨LinearEquiv.ofLinear φ ψ (LinearMap.ext h1) (LinearMap.ext h2), ?_, hφu⟩
  intro x y
  show Algebra.trace ℚ K (h (φ x) (φ y)) = Algebra.trace ℚ K (h x y)
  obtain ⟨s, hs⟩ := classSetAssembly_span h hpos ι hι u hu y
  have hφy : φ y = ∑ j, (s j : K) • u' j := by
    rw [hs, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hφu j]
  rw [hφy, hs, classSetAssembly_tr_sum_right, classSetAssembly_tr_sum_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [classSetAssembly_tr_qsmul_right, classSetAssembly_tr_qsmul_right, hφ]
end Formalism.HermitianLatticesTheory
