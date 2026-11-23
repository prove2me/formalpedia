-- Prove2me | solution 1 for Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.frameMat_herm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:03.82644+00:00
-- url     : https://prove2.me/submissions/acdbd474-2901-4fd4-b257-3fcb32814bc1

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.ExtensionFiltration
open Formalism.HN
open Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
namespace Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (e : V →ₗ[K] V) (v : InfinitePlace K)
    (hsa : ∀ x y, Formalism.HermitianLatticesTheory.majAt b X v (e x) y = Formalism.HermitianLatticesTheory.majAt b X v x (e y)) :
    ((X v)⁻¹ * (LinearMap.toMatrix b b e).map v.embedding * X v).IsHermitian := by
  have hXU : X v * (X v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (hX v)
  have hUu : IsUnit ((X v)⁻¹).det := Matrix.isUnit_nonsing_inv_det _ (hX v)
  set U := (X v)⁻¹ with hUdef
  set M := (LinearMap.toMatrix b b e).map v.embedding with hMdef
  have hcol : ∀ k l, (U.mulVec (fun i => v.embedding ((b.repr (b k)) i))) l = U l k := by
    intro k l
    have hv : (fun i => v.embedding ((b.repr (b k)) i)) = Pi.single k 1 := by
      funext i
      by_cases h : i = k
      · subst h
        simp
      · simp [Finsupp.single_apply, Pi.single_apply, h, Ne.symm h]
    rw [hv]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hcolM : ∀ k l, (U.mulVec (fun i => v.embedding ((b.repr (e (b k))) i))) l = (U * M) l k := by
    intro k l
    have hv2 : (fun i => v.embedding ((b.repr (e (b k))) i)) = fun i => M i k := by
      funext i
      rw [hMdef, Matrix.map_apply, LinearMap.toMatrix_apply]
    rw [hv2]
    rfl
  have key : (U * M).conjTranspose * U = U.conjTranspose * (U * M) := by
    ext k l
    have h := hsa (b k) (b l)
    unfold Formalism.HermitianLatticesTheory.majAt Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt at h
    rw [← hUdef] at h
    simp only [hcol, hcolM] at h
    rw [Matrix.mul_apply, Matrix.mul_apply]
    exact h
  have hUHu : IsUnit U.conjTranspose.det := by
    rw [Matrix.det_conjTranspose]
    exact hUu.star
  have hFU : U * M * X v * U = U * M := by
    rw [Matrix.mul_assoc (U * M), hXU, Matrix.mul_one]
  have key2 : U.conjTranspose * (U * M * X v).conjTranspose * U = U.conjTranspose * (U * M * X v) * U := by
    calc U.conjTranspose * (U * M * X v).conjTranspose * U = (U * M * X v * U).conjTranspose * U := by
          rw [Matrix.conjTranspose_mul (U * M * X v) U]
      _ = (U * M).conjTranspose * U := by rw [hFU]
      _ = U.conjTranspose * (U * M) := key
      _ = U.conjTranspose * (U * M * X v * U) := by rw [hFU]
      _ = U.conjTranspose * (U * M * X v) * U := by simp only [Matrix.mul_assoc]
  have hinvL : (U.conjTranspose)⁻¹ * U.conjTranspose = 1 := Matrix.nonsing_inv_mul _ hUHu
  have hinvR : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv _ hUu
  unfold Matrix.IsHermitian
  calc (U * M * X v).conjTranspose = (U.conjTranspose)⁻¹ * (U.conjTranspose * (U * M * X v).conjTranspose * U) * U⁻¹ := by
        simp only [Matrix.mul_assoc]
        rw [hinvR, Matrix.mul_one, ← Matrix.mul_assoc (U.conjTranspose)⁻¹, hinvL, Matrix.one_mul]
    _ = (U.conjTranspose)⁻¹ * (U.conjTranspose * (U * M * X v) * U) * U⁻¹ := by rw [key2]
    _ = U * M * X v := by
        simp only [Matrix.mul_assoc]
        rw [hinvR, Matrix.mul_one, ← Matrix.mul_assoc (U.conjTranspose)⁻¹, hinvL, Matrix.one_mul]
end Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
