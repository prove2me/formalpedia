-- Prove2me | solution 1 for Formalism.HN.PlaceDecomposition.finrank_span_complex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:17.376525+00:00
-- url     : https://prove2.me/submissions/b620f91f-1ee8-4820-b8f8-825271d7fe8f

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Theorems.Thm_Formalism_HN_PlaceDecomposition_li_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.PlaceDecomposition
variable {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.HN.PlaceDecomposition
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (N : Submodule (𝓞 K) V) (v : InfinitePlace K) :
    finrank ℂ (Submodule.span ℂ (Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V))) = rkK N := by
  classical
  have hA : Function.Injective (Matrix.mulVecLin (X v)⁻¹) := by
    intro a c h
    have h' := congrArg (Matrix.mulVec (X v)) h
    simpa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hX v)] using h'
  have himg : Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V) =
      (Matrix.mulVecLin (X v)⁻¹) '' (Formalism.HermitianLatticesTheory.vecAt b v '' (N : Set V)) := by
    rw [Set.image_image]
    rfl
  rw [himg, ← Submodule.map_span, ← (Submodule.equivMapOfInjective _ hA _).finrank_eq]
  haveI : Module.Finite K V := Module.Finite.of_basis b
  obtain ⟨t, htN, hspan, hli⟩ := exists_linearIndependent K (N : Set V)
  haveI : Fintype t := by
    first
      | exact hli.setFinite.fintype
      | exact @Fintype.ofFinite _ hli.finite
  have hadd : ∀ x y : V, Formalism.HermitianLatticesTheory.vecAt b v (x + y) =
      Formalism.HermitianLatticesTheory.vecAt b v x + Formalism.HermitianLatticesTheory.vecAt b v y := by
    intro x y
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt]
  have hsmul : ∀ (a : K) (x : V), Formalism.HermitianLatticesTheory.vecAt b v (a • x) =
      v.embedding a • Formalism.HermitianLatticesTheory.vecAt b v x := by
    intro a x
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt, map_mul]
  have hzero : Formalism.HermitianLatticesTheory.vecAt b v 0 = 0 := by
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt]
  let y : t → ι → ℂ := fun j => Formalism.HermitianLatticesTheory.vecAt b v (j : V)
  have hliC : LinearIndependent ℂ y := by
    have h1 : LinearIndependent K (fun j : t => b.equivFun (j : V)) :=
      hli.map' b.equivFun.toLinearMap b.equivFun.ker
    have h2 := li_map v.embedding (fun (j : t) (i : ι) => b.equivFun (j : V) i) h1
    have h3 : y = fun (j : t) (i : ι) => v.embedding (b.equivFun (j : V) i) := by
      funext j i
      simp [y, Formalism.HermitianLatticesTheory.vecAt, Basis.equivFun_apply]
    rw [h3]
    exact h2
  have hsp : Submodule.span ℂ (Formalism.HermitianLatticesTheory.vecAt b v '' (N : Set V)) =
      Submodule.span ℂ (Set.range y) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      let Q : Submodule K V :=
        { carrier := {x | Formalism.HermitianLatticesTheory.vecAt b v x ∈ Submodule.span ℂ (Set.range y)}
          add_mem' := fun {a c} ha hc => by
            show Formalism.HermitianLatticesTheory.vecAt b v (a + c) ∈ Submodule.span ℂ (Set.range y)
            rw [hadd]
            exact Submodule.add_mem _ ha hc
          zero_mem' := by
            show Formalism.HermitianLatticesTheory.vecAt b v 0 ∈ Submodule.span ℂ (Set.range y)
            rw [hzero]
            exact Submodule.zero_mem _
          smul_mem' := fun a c hc => by
            show Formalism.HermitianLatticesTheory.vecAt b v (a • c) ∈ Submodule.span ℂ (Set.range y)
            rw [hsmul]
            exact Submodule.smul_mem _ _ hc }
      have hle : Submodule.span K t ≤ Q := by
        rw [Submodule.span_le]
        intro j hj
        exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
      have hx' : x ∈ Submodule.span K t := by
        rw [hspan]
        exact Submodule.subset_span hx
      exact hle hx'
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact Submodule.subset_span ⟨(j : V), htN j.2, rfl⟩
  rw [hsp, finrank_span_eq_card hliC]
  unfold rkK
  rw [← hspan]
  have h3 := finrank_span_eq_card hli
  first
    | rw [Subtype.range_coe] at h3
    | rw [Subtype.range_val] at h3
    | simp only [Subtype.range_coe_subtype, Set.setOf_mem_eq] at h3
  exact h3.symm
end Formalism.HN.PlaceDecomposition
