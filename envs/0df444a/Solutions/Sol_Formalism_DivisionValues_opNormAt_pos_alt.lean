-- Prove2me | solution 1 for Formalism.DivisionValues.opNormAt_pos_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:22.473955+00:00
-- url     : https://prove2.me/submissions/881af3de-e627-4ba4-a02e-b44cf0a0ac01

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_PassageScaleFree
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_KappaNormalise

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.DivisionValues
theorem _root_.solution [StarRing K] {n D : ℕ}
    (XN : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (Y : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (v : InfinitePlace K)
    (hXN : IsUnit (XN v).det) (hY : IsUnit (Y v).det)
    (φ : (Fin n → K) →ₗ[K] Module.Dual K (Fin D → K)) (hφ : φ ≠ 0) :
    0 < Formalism.HN.opNormAt (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis Y v φ := by
  unfold Formalism.HN.opNormAt
  rw [norm_pos_iff]
  intro h0
  apply hφ
  have hA : (Y v)⁻¹ * (LinearMap.toMatrix (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin D)).dualBasis
      φ).map v.embedding * XN v = 0 :=
    (Matrix.toEuclideanLin).map_eq_zero_iff.mp (LinearMap.toContinuousLinearMap.map_eq_zero_iff.mp h0)
  have hM : (LinearMap.toMatrix (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin D)).dualBasis
      φ).map v.embedding = 0 := by
    have e1 : (LinearMap.toMatrix (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin D)).dualBasis
        φ).map v.embedding = Y v * ((Y v)⁻¹ * (LinearMap.toMatrix (Pi.basisFun K (Fin n))
        (Pi.basisFun K (Fin D)).dualBasis φ).map v.embedding * XN v) * (XN v)⁻¹ := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hY, Matrix.one_mul,
        Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hXN, Matrix.mul_one]
    rw [e1, hA, Matrix.mul_zero, Matrix.zero_mul]
  have hT : LinearMap.toMatrix (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin D)).dualBasis φ = 0 := by
    ext i j
    have h1 := congrArg (fun A => A i j) hM
    simp only [Matrix.map_apply, Matrix.zero_apply] at h1
    exact (map_eq_zero_iff _ v.embedding.injective).mp h1
  exact (LinearMap.toMatrix _ _).map_eq_zero_iff.mp hT
end Formalism.DivisionValues
