-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.classSetAssembly_nondeg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:33:10.662429+00:00
-- url     : https://prove2.me/submissions/41671563-e96c-488a-8cea-5840fed29f32

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetAssembly
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
private theorem span_eq_top_of_li_lemma {n : ℕ} (w : Fin n → EuclideanSpace ℝ (Fin n))
    (hw : LinearIndependent ℝ w) : Submodule.span ℝ (Set.range w) = ⊤ := by
  have hc : Fintype.card (Fin n) = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by simp
  exact hw.span_eq_top_of_card_eq_finrank' hc
private theorem eq_zero_of_inner_li_lemma_2 {n : ℕ} (w : Fin n → EuclideanSpace ℝ (Fin n))
    (hw : LinearIndependent ℝ w) (v : EuclideanSpace ℝ (Fin n))
    (hv : ∀ j, inner ℝ v (w j) = 0) : v = 0 := by
  have hs := span_eq_top_of_li_lemma w hw
  obtain ⟨b, hb⟩ : ∃ b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)), ∀ i, b i = w i :=
    ⟨Basis.mk hw (by rw [hs]), fun i => by simp [Basis.mk_apply]⟩
  have key : inner ℝ v (∑ i, b.repr v i • b i) = 0 := by
    rw [inner_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [inner_smul_right, hb i, hv i, mul_zero]
  rw [b.sum_repr v] at key
  exact inner_self_eq_zero.mp key
end Real
section Finite
variable {V : Type*} [AddCommGroup V]
end Finite
section Isom
variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
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
    (u : Fin n → V) (hu : LinearIndependent ℝ (ι ∘ u)) (y : V)
    (hy : ∀ j, Algebra.trace ℚ K (h y (u j)) = 0) : y = 0 := by
  have h0 : ι y = 0 := eq_zero_of_inner_li_lemma_2 (ι ∘ u) hu (ι y) (fun j => by
    rw [Function.comp_apply, hι, hy j, Rat.cast_zero])
  by_contra hne
  have hp := hpos y hne
  have h2 : ((Algebra.trace ℚ K (h y y) : ℚ) : ℝ) = 0 := by rw [← hι, h0, inner_zero_left]
  have h3 : Algebra.trace ℚ K (h y y) = 0 := by exact_mod_cast h2
  rw [h3] at hp
  exact lt_irrefl _ hp
end Formalism.HermitianLatticesTheory
