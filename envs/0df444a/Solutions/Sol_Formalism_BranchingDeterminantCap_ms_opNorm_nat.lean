-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.ms_opNorm_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:15.014563+00:00
-- url     : https://prove2.me/submissions/e5eee270-453a-422a-ba9a-7bce2696c879

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open Formalism.HN
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution [Nonempty ι] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (n : ℕ) (v : InfinitePlace K) :
    opNormAt b X b X v ((n : K) • (LinearMap.id : V →ₗ[K] V)) = n := by
  have h1 : (LinearMap.toMatrix b b ((n : K) • (LinearMap.id : V →ₗ[K] V))).map v.embedding
      = (n : ℂ) • (1 : Matrix ι ι ℂ) := by
    ext i j
    by_cases h : i = j <;> simp [LinearMap.toMatrix_id, Matrix.one_apply, h]
  have hM : (X v)⁻¹ * (LinearMap.toMatrix b b ((n : K) • (LinearMap.id : V →ₗ[K] V))).map
      v.embedding * X v = (n : ℂ) • (1 : Matrix ι ι ℂ) := by
    rw [h1, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.nonsing_inv_mul _ (hX v)]
  have h3 : Matrix.toEuclideanLin (1 : Matrix ι ι ℂ) = LinearMap.id := by
    first
      | exact Matrix.toEuclideanLin_one
      | (ext x i; simp [Matrix.toEuclideanLin_apply])
      | (simp [Matrix.toEuclideanLin, Matrix.toLin'_one])
  have h4 : LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin ((n : ℂ) • (1 : Matrix ι ι ℂ)))
      = (n : ℂ) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ ι) := by
    rw [map_smul, h3, map_smul]
    congr 1
  unfold Formalism.HN.opNormAt
  rw [hM, h4, norm_smul]
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  have hid : ‖ContinuousLinearMap.id ℂ (EuclideanSpace ℂ ι)‖ = 1 := by
    first
      | exact ContinuousLinearMap.norm_id
      | (apply ContinuousLinearMap.norm_id_of_nontrivial_seminorm
         exact ⟨EuclideanSpace.single i 1, by simp⟩)
  rw [hid, mul_one]
  simp
end Formalism.BranchingDeterminantCap
