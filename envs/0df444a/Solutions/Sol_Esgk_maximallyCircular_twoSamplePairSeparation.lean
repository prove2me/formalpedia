-- Prove2me | solution 1 for Esgk.maximallyCircular_twoSamplePairSeparation
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-16T05:10:53.906522+00:00
-- url     : https://prove2.me/submissions/b7ad5c3e-c373-4149-ba5e-55d03c6863cc

 
import Definitions.Def_Esgk_AffineLinePolynomialRestriction
import Definitions.Def_Esgk_AuxiliaryCircleNoncontainment
import Definitions.Def_Esgk_AuxiliaryIncidenceDeletion
import Definitions.Def_Esgk_BidegreeProductRelation
import Definitions.Def_Esgk_BivariateCornerNormalForm
import Definitions.Def_Esgk_BridgeIdentity
import Definitions.Def_Esgk_CirclePolynomialRestriction
import Definitions.Def_Esgk_CircleRationalParametrization
import Definitions.Def_Esgk_CircularJTangentConjugation
import Definitions.Def_Esgk_CircularTangentIsotropicFaces
import Definitions.Def_Esgk_CollisionRootGroupoid
import Definitions.Def_Esgk_CommonImageFunctionFieldAutomorphism
import Definitions.Def_Esgk_CommonImageFunctionFieldAutomorphismSourceEquiv
import Definitions.Def_Esgk_ComplexPlaneConjugationDescent
import Definitions.Def_Esgk_ComplexPlaneProjectiveHomogenization
import Definitions.Def_Esgk_ConnectedLocalHomeomorphReal
import Definitions.Def_Esgk_DirectIsometryClassification
import Definitions.Def_Esgk_DistanceDeficiencyNewton
import Definitions.Def_Esgk_DistanceDesign
import Definitions.Def_Esgk_DistanceNewtonElementaryPolynomial
import Definitions.Def_Esgk_DistanceNewtonFactorSaturation
import Definitions.Def_Esgk_DistanceNewtonITangentHomogeneousForm
import Definitions.Def_Esgk_DistanceNewtonPersistentTangentRoots
import Definitions.Def_Esgk_DistanceNewtonPowerSumPolynomial
import Definitions.Def_Esgk_DistanceSquaredMissingMultiset
import Definitions.Def_Esgk_Energy
import Definitions.Def_Esgk_FiniteBoundaryCurveComponents
import Definitions.Def_Esgk_FiniteIncidenceCodegreeBound
import Definitions.Def_Esgk_FiniteRealCutIntervals
import Definitions.Def_Esgk_Foundation
import Definitions.Def_Esgk_IntegralClosureAutomorphism
import Definitions.Def_Esgk_IntrinsicPartitionScale
import Definitions.Def_Esgk_IrreduciblePlaneAffineFunctionField
import Definitions.Def_Esgk_IrreduciblePlaneAffineIsometryDistanceTransport
import Definitions.Def_Esgk_IrreduciblePlaneAffineIsometryTransport
import Definitions.Def_Esgk_IrreduciblePlaneAffineNormalization
import Definitions.Def_Esgk_IrreduciblePlaneAffineNormalizationAutomorphism
import Definitions.Def_Esgk_IrreduciblePlaneAffineNormalizationDistanceAction
import Definitions.Def_Esgk_IrreduciblePlaneAffineNormalizationNonsingularLift
import Definitions.Def_Esgk_IrreduciblePlaneAffineNormalizationRealEvaluation
import Definitions.Def_Esgk_IrreduciblePlaneAffineNormalizationSmoothRealLift
import Definitions.Def_Esgk_IrreduciblePlaneDistanceImageDegreeOne
import Definitions.Def_Esgk_IrreduciblePlaneDistanceImageField
import Definitions.Def_Esgk_IrreduciblePlaneDistanceImageIdealTransport
import Definitions.Def_Esgk_IrreduciblePlaneDistanceImageInfiniteCorrespondence
import Definitions.Def_Esgk_IrreduciblePlaneDistanceImagePrimeComponent
import Definitions.Def_Esgk_IrreduciblePlaneFunctionField
import Definitions.Def_Esgk_IrreduciblePlaneInfiniteVanishing
import Definitions.Def_Esgk_IrreduciblePlaneNormalizedDistanceImagePullback
import Definitions.Def_Esgk_IrreduciblePlanePolynomialAlgEquivTransport
import Definitions.Def_Esgk_IrreduciblePlaneTwoPairCoordinateIntegrality
import Definitions.Def_Esgk_MatchingExtraction
import Definitions.Def_Esgk_MaximallyCircularAuxiliaryCodegree
import Definitions.Def_Esgk_MaximallyCircularCurveDistinctDistances
import Definitions.Def_Esgk_MaximallyCircularDegreeTwoCircle
import Definitions.Def_Esgk_MaximallyCircularIntrinsicCellCover
import Definitions.Def_Esgk_MaximallyCircularIsotropicBidegree
import Definitions.Def_Esgk_MaximallyCircularLargeScaleIncidence
import Definitions.Def_Esgk_MaximallyCircularQuarticBootstrap
import Definitions.Def_Esgk_MaximallyCircularQuarticFromIncidence
import Definitions.Def_Esgk_MultivariateEliminationResultant
import Definitions.Def_Esgk_MvPolynomialLocalOrder
import Definitions.Def_Esgk_NewtonElementaryFromPowerSums
import Definitions.Def_Esgk_NonabsolutePlanePointBound
import Definitions.Def_Esgk_NormalizedDistancePairInfiniteProjection
import Definitions.Def_Esgk_NormalizedFactorPointSelection
import Definitions.Def_Esgk_PachDeZeeuwCurveSymmetryCommonCenter
import Definitions.Def_Esgk_PachDeZeeuwCurveSymmetryReduction
import Definitions.Def_Esgk_PachDeZeeuwCurveSymmetryTranslation
import Definitions.Def_Esgk_PachDeZeeuwQuadraticDegree
import Definitions.Def_Esgk_PlanarGeneralPosition
import Definitions.Def_Esgk_PlaneAffineIsometryDistancePolynomial
import Definitions.Def_Esgk_PlaneAffineIsometryPolynomial
import Definitions.Def_Esgk_PlaneAffineLinePolynomial
import Definitions.Def_Esgk_PlaneCircleFactor
import Definitions.Def_Esgk_PlaneCircularLocalChart
import Definitions.Def_Esgk_PlaneCircularLocalOrderDegree
import Definitions.Def_Esgk_PlaneCurveArcPartition
import Definitions.Def_Esgk_PlaneCurveCellVisits
import Definitions.Def_Esgk_PlaneCurveExceptionalSample
import Definitions.Def_Esgk_PlaneCurveGradientCutoff
import Definitions.Def_Esgk_PlaneCurveRadialChart
import Definitions.Def_Esgk_PlaneCurveRadialCritical
import Definitions.Def_Esgk_PlaneCurveRadiusFibers
import Definitions.Def_Esgk_PlaneCurveRegularChart
import Definitions.Def_Esgk_PlaneCurveSafeComponents
import Definitions.Def_Esgk_PlaneCurveSafeSample
import Definitions.Def_Esgk_PlaneHorizontalReflection
import Definitions.Def_Esgk_PlaneIsometryFixedPointBisector
import Definitions.Def_Esgk_PlaneIsotropicCoordinates
import Definitions.Def_Esgk_PlaneNonabsoluteRealPointBound
import Definitions.Def_Esgk_PlanePolynomialRationalPullback
import Definitions.Def_Esgk_PlaneProjectiveAffineChart
import Definitions.Def_Esgk_PlaneProjectiveHomogenization
import Definitions.Def_Esgk_PlaneProjectiveModel
import Definitions.Def_Esgk_PlaneRadialFiltration
import Definitions.Def_Esgk_PlaneRadialQuadratic
import Definitions.Def_Esgk_RadialFiltrationCircularMultiplicity
import Definitions.Def_Esgk_RichnessLevels
import Definitions.Def_Esgk_SelfCurveCompleteSymmetryFamily
import Definitions.Def_Esgk_SelfCurveDistancePairNormalization
import Definitions.Def_Esgk_SelfCurveDistancePairs
import Definitions.Def_Esgk_SelfCurveExceptionalAnchors
import Definitions.Def_Esgk_SelfCurveExceptionalIsometryFamilies
import Definitions.Def_Esgk_SelfCurveFunctionFieldSymmetry
import Definitions.Def_Esgk_SelfCurveReflectionInvariance
import Definitions.Def_Esgk_SelfCurveRetainedNonreflection
import Definitions.Def_Esgk_SelfCurveReversingSymmetryFamily
import Definitions.Def_Esgk_SelfCurveTwoAnchorFunctionField
import Definitions.Def_Esgk_SharpResultantFiniteSetCount
import Definitions.Def_Esgk_TwoPairDistanceCarrierSymmetry
import Definitions.Def_Esgk_TwoPairDistanceQuadricCharts
import Definitions.Def_Esgk_TwoPairDistanceQuadricPolynomialPullback
import Definitions.Def_LeanFormalizations_Combinatorics_CombinatorialMap_Basic
import Definitions.Def_LeanFormalizations_Combinatorics_CombinatorialMap_EdgeInsertion
import Definitions.Def_LeanFormalizations_Combinatorics_CombinatorialMap_PlanarEdgeBound
import Definitions.Def_LeanFormalizations_Geometry_Euclidean_IsometryClassification
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves
import Definitions.Def_LeanFormalizations_PachDeZeeuw_Basic
import Definitions.Def_LeanFormalizations_PachDeZeeuw_Bezout
import Definitions.Def_LeanFormalizations_PachDeZeeuw_ChartBridge
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CrossingLemma_PLCover
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CrossingLemma_PlaneArcSeparation
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CrossingLemma_Shear
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearExists
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearIrreducible
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CurveInterface
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CurveSymmetries
import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Topology.MetricSpace.Isometry

 
section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

variable {F L K : Type*}
variable [Field F] [Field L] [Field K]
variable [Algebra F L] [Algebra F K]


@[simp]
theorem commonImageFunctionFieldAutomorphism_apply_second
    (φ₁ φ₂ : L →ₐ[F] K)
    (hφ₁ : Function.Surjective φ₁)
    (hφ₂ : Function.Surjective φ₂)
    (x : L) :
    commonImageFunctionFieldAutomorphism φ₁ φ₂ hφ₁ hφ₂ (φ₂ x) = φ₁ x := by
  change φ₁ ((AlgEquiv.ofBijective φ₂
    ⟨RingHom.injective φ₂.toRingHom, hφ₂⟩).symm (φ₂ x)) = φ₁ x
  exact congrArg φ₁
    ((AlgEquiv.ofBijective φ₂
      ⟨RingHom.injective φ₂.toRingHom, hφ₂⟩).symm_apply_apply x)


end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk


theorem eval_eq_eval_specializeRemainingVariables {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) (z : Fin (n + 1) → ℝ) :
    MvPolynomial.eval z p =
      Polynomial.eval (z 0) (specializeRemainingVariables (fun i ↦ z i.succ) p) := by
  have hcons : Fin.cons (z 0) (fun i : Fin n ↦ z i.succ) = z := by
    funext i
    exact Fin.cases (by simp) (fun j ↦ by simp) i
  calc
    MvPolynomial.eval z p =
        MvPolynomial.eval (Fin.cons (z 0) (fun i : Fin n ↦ z i.succ)) p := by rw [hcons]
    _ = Polynomial.eval (z 0) (specializeRemainingVariables (fun i ↦ z i.succ) p) := by
      simpa [specializeRemainingVariables, headCurry] using
        (MvPolynomial.eval_eq_eval_mv_eval'
          (s := fun i : Fin n ↦ z i.succ) (y := z 0) p)

 
theorem resultant_specializeRemainingVariables {n : ℕ}
    (p q : MvPolynomial (Fin (n + 1)) ℝ) (x : Fin n → ℝ) :
    Polynomial.resultant (specializeRemainingVariables x p) (specializeRemainingVariables x q)
        (headCurry p).natDegree (headCurry q).natDegree =
      MvPolynomial.eval x (headResultant p q) := by
  rw [specializeRemainingVariables, headResultant]
  exact Polynomial.resultant_map_map (headCurry p) (headCurry q)
    (headCurry p).natDegree (headCurry q).natDegree (MvPolynomial.eval x)

 
theorem eval_headResultant_eq_zero_of_common_zero {n : ℕ}
    (p q : MvPolynomial (Fin (n + 1)) ℝ) (z : Fin (n + 1) → ℝ)
    (hpDegree : 0 < (headCurry p).natDegree)
    (hp : MvPolynomial.eval z p = 0) (hq : MvPolynomial.eval z q = 0) :
    MvPolynomial.eval (fun i ↦ z i.succ) (headResultant p q) = 0 := by
  have hpSpecialized :
      Polynomial.eval (z 0) (specializeRemainingVariables (fun i ↦ z i.succ) p) = 0 := by
    rw [← eval_eq_eval_specializeRemainingVariables]
    exact hp
  have hqSpecialized :
      Polynomial.eval (z 0) (specializeRemainingVariables (fun i ↦ z i.succ) q) = 0 := by
    rw [← eval_eq_eval_specializeRemainingVariables]
    exact hq
  have hpDegreeLe :
      (specializeRemainingVariables (fun i ↦ z i.succ) p).natDegree ≤
        (headCurry p).natDegree := by
    simpa [specializeRemainingVariables] using
      (Polynomial.natDegree_map_le
        (f := MvPolynomial.eval (fun i ↦ z i.succ)) (p := headCurry p))
  have hqDegreeLe :
      (specializeRemainingVariables (fun i ↦ z i.succ) q).natDegree ≤
        (headCurry q).natDegree := by
    simpa [specializeRemainingVariables] using
      (Polynomial.natDegree_map_le
        (f := MvPolynomial.eval (fun i ↦ z i.succ)) (p := headCurry q))
  obtain ⟨u, v, _, _, hbezout⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant
      (f := specializeRemainingVariables (fun i ↦ z i.succ) p)
      (g := specializeRemainingVariables (fun i ↦ z i.succ) q)
      hpDegreeLe hqDegreeLe (Or.inl (Nat.ne_of_gt hpDegree))
  have hresultant :
      Polynomial.resultant
          (specializeRemainingVariables (fun i ↦ z i.succ) p)
          (specializeRemainingVariables (fun i ↦ z i.succ) q)
          (headCurry p).natDegree (headCurry q).natDegree = 0 := by
    have hzero :
        Polynomial.eval (z 0)
            (Polynomial.C
              (Polynomial.resultant
                (specializeRemainingVariables (fun i ↦ z i.succ) p)
                (specializeRemainingVariables (fun i ↦ z i.succ) q)
                (headCurry p).natDegree (headCurry q).natDegree)) = 0 := by
      rw [← hbezout]
      simp [hpSpecialized, hqSpecialized]
    simpa using hzero
  rw [← resultant_specializeRemainingVariables]
  exact hresultant

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open _root_.Polynomial


theorem Polynomial.roots_toFinset_card_pos_of_natDegree_pos
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (q : Polynomial K) (hq : 0 < q.natDegree) :
    0 < q.roots.toFinset.card := by
  have hroots_card : q.roots.card = q.natDegree :=
    IsAlgClosed.card_roots_eq_natDegree
  have hroots_ne : q.roots ≠ 0 := by
    intro hzero
    rw [hzero] at hroots_card
    simp at hroots_card
    omega
  exact Finset.card_pos.mpr (Multiset.toFinset_nonempty.mpr hroots_ne)


end Esgk

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open _root_.Polynomial


theorem Polynomial.eq_C_leadingCoeff_mul_X_sub_C_pow_natDegree_of_roots_toFinset_eq_singleton
    (p : ℂ[X]) (_hp : p ≠ 0) {τ : ℂ} (hτ : p.roots.toFinset = {τ}) :
    p = C p.leadingCoeff * (X - C τ) ^ p.natDegree := by
  classical
  have hroots : p.roots = Multiset.replicate p.roots.card τ := by
    apply Multiset.eq_replicate_card.mpr
    intro z hz
    have hz' : z ∈ p.roots.toFinset := Multiset.mem_toFinset.mpr hz
    simpa [hτ] using hz'
  calc
    p = C p.leadingCoeff * (p.roots.map (X - C ·)).prod :=
      (IsAlgClosed.splits p).eq_prod_roots
    _ = C p.leadingCoeff * (X - C τ) ^ p.natDegree := by
      rw [hroots, Multiset.map_replicate, Multiset.prod_replicate,
        IsAlgClosed.card_roots_eq_natDegree]


theorem Polynomial.exists_eq_C_leadingCoeff_mul_X_sub_C_pow_natDegree_of_roots_toFinset_card_eq_one
    (p : ℂ[X]) (_hp : p ≠ 0) (hcard : p.roots.toFinset.card = 1) :
    ∃ τ : ℂ, p = C p.leadingCoeff * (X - C τ) ^ p.natDegree := by
  classical
  obtain ⟨τ, hτ⟩ := Finset.card_eq_one.mp hcard
  exact ⟨τ,
    Polynomial.eq_C_leadingCoeff_mul_X_sub_C_pow_natDegree_of_roots_toFinset_eq_singleton
      p _hp hτ⟩

end Esgk

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk


theorem twoAnchor_sqDistance_eq_same_or_reflection
    {a x₁ y₁ x₂ y₂ : ℝ}
    (ha : 0 < a)
    (h₁ : (x₁ + a) ^ 2 + y₁ ^ 2 = (x₂ + a) ^ 2 + y₂ ^ 2)
    (h₂ : (x₁ - a) ^ 2 + y₁ ^ 2 = (x₂ - a) ^ 2 + y₂ ^ 2) :
    (x₁ = x₂ ∧ y₁ = y₂) ∨ (x₁ = x₂ ∧ y₁ = -y₂) := by
  have hx : x₁ = x₂ := by
    nlinarith [h₁, h₂]
  have hy_sq : y₁ ^ 2 = y₂ ^ 2 := by
    nlinarith [h₁, hx]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy_sq with hy | hy
  · exact Or.inl ⟨hx, hy⟩
  · exact Or.inr ⟨hx, hy⟩


theorem exceptionalOrderedPairs_card_le {α : Type*} [DecidableEq α]
    (S degreeRight : Finset α) :
    (exceptionalOrderedPairs S degreeRight).card ≤ 2 * degreeRight.card * S.card := by
  unfold exceptionalOrderedPairs
  calc
    ((degreeRight ×ˢ S) ∪ (S ×ˢ degreeRight)).card ≤
        (degreeRight ×ˢ S).card + (S ×ˢ degreeRight).card :=
      Finset.card_union_le _ _
    _ = 2 * degreeRight.card * S.card := by
      simp only [Finset.card_product]
      ring


theorem deletedIndexedPairs_card_le {α : Type*} [DecidableEq α]
    (S degreeRight : Finset α) (Γ : Finset (α × α)) {B G : ℕ}
    (hE : degreeRight.card ≤ B) (hΓ : Γ.card ≤ G) :
    (deletedIndexedPairs S degreeRight Γ).card ≤ 2 * B * S.card + G := by
  unfold deletedIndexedPairs
  calc
    (exceptionalOrderedPairs S degreeRight ∪ Γ).card ≤
        (exceptionalOrderedPairs S degreeRight).card + Γ.card :=
      Finset.card_union_le _ _
    _ ≤ 2 * degreeRight.card * S.card + Γ.card :=
      Nat.add_le_add_right (exceptionalOrderedPairs_card_le S degreeRight) Γ.card
    _ ≤ 2 * B * S.card + G :=
      Nat.add_le_add
        (Nat.mul_le_mul_right S.card (Nat.mul_le_mul_left 2 hE)) hΓ


theorem deletedIndexedPairs_card_le_eight_mul_degree_sq
    {α : Type*} [DecidableEq α]
    (S singular axis : Finset α) (Γ : Finset (α × α)) {d : ℕ}
    (hd : 2 ≤ d)
    (hsingular : singular.card ≤ d * (d - 1))
    (haxis : axis.card ≤ 2 * d ^ 2)
    (hΓ : Γ.card ≤ 4 * d * S.card) :
    (deletedIndexedPairs S (singular ∪ axis) Γ).card ≤
      8 * d ^ 2 * S.card := by
  have hsingular' : singular.card ≤ d ^ 2 := by
    calc
      singular.card ≤ d * (d - 1) := hsingular
      _ ≤ d * d := Nat.mul_le_mul_left d (Nat.sub_le d 1)
      _ = d ^ 2 := by ring
  have hE : (singular ∪ axis).card ≤ 3 * d ^ 2 := by
    calc
      (singular ∪ axis).card ≤ singular.card + axis.card :=
        Finset.card_union_le _ _
      _ ≤ d ^ 2 + 2 * d ^ 2 :=
        Nat.add_le_add hsingular' haxis
      _ = 3 * d ^ 2 := by ring
  have hbase := deletedIndexedPairs_card_le
    S (singular ∪ axis) Γ hE hΓ
  have hΓ' : 4 * d * S.card ≤ 2 * d ^ 2 * S.card := by
    apply Nat.mul_le_mul_right S.card
    calc
      4 * d ≤ (2 * d) * d := by
        exact Nat.mul_le_mul_right d (by omega)
      _ = 2 * d ^ 2 := by ring
  calc
    (deletedIndexedPairs S (singular ∪ axis) Γ).card
        ≤ 2 * (3 * d ^ 2) * S.card + 4 * d * S.card := hbase
    _ ≤ 2 * (3 * d ^ 2) * S.card + 2 * d ^ 2 * S.card :=
      Nat.add_le_add_left hΓ' _
    _ = 8 * d ^ 2 * S.card := by ring


theorem anchor_image_eq_of_sqDistance_pullback
    {X P : Type*} [MetricSpace P]
    {ν : X → P} {T : X → X} {x : X} {p q : P}
    (hν : ν x = p)
    (hpullback : ∀ y, dist (ν y) p ^ 2 = dist (ν (T y)) q ^ 2) :
    ν (T x) = q := by
  have hzero : dist (ν (T x)) q ^ 2 = 0 := by
    simpa [hν] using (hpullback x).symm
  have hdist : dist (ν (T x)) q = 0 := by
    nlinarith [sq_nonneg (dist (ν (T x)) q)]
  exact dist_eq_zero.mp hdist


end Esgk

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open MvPolynomial


@[simp]
theorem bivariateCornerExponent_zero (p : ℕ) : bivariateCornerExponent p 0 = p := by
  simp [bivariateCornerExponent]

@[simp]
theorem bivariateCornerExponent_one (p : ℕ) : bivariateCornerExponent p 1 = p := by
  simp [bivariateCornerExponent]


theorem coeff_bivariateCornerRemainder (p : ℕ) (Q : BidegreePolynomial ℂ)
    (e : Fin 2 →₀ ℕ) :
    coeff e (bivariateCornerRemainder p Q) =
      if e = bivariateCornerExponent p then 0 else coeff e Q := by
  rw [bivariateCornerRemainder, coeff_sub, coeff_monomial]
  by_cases he : e = bivariateCornerExponent p
  · subst e
    simp
  · simp [he, Ne.symm he]

@[simp]
theorem coeff_bivariateCornerRemainder_corner (p : ℕ) (Q : BidegreePolynomial ℂ) :
    coeff (bivariateCornerExponent p) (bivariateCornerRemainder p Q) = 0 := by
  simp [coeff_bivariateCornerRemainder]

 
theorem coeff_bivariateCornerExponent_ne_zero (Q : BidegreePolynomial ℂ) (p : ℕ)
    (hp : 0 < p) (hbound : BidegreeBound p Q) (htotal : Q.totalDegree = 2 * p) :
    coeff (bivariateCornerExponent p) Q ≠ 0 := by
  have hQ : Q ≠ 0 := by
    intro hzero
    subst Q
    simp at htotal
    omega
  obtain ⟨e, he, hmax⟩ :=
    Finset.exists_mem_eq_sup Q.support (MvPolynomial.support_nonempty.mpr hQ)
      (fun e ↦ e.sum fun _ k ↦ k)
  have hesum : e.sum (fun _ k ↦ k) = 2 * p := by
    calc
      e.sum (fun _ k ↦ k) = Q.support.sup (fun e ↦ e.sum fun _ k ↦ k) := hmax.symm
      _ = Q.totalDegree := rfl
      _ = 2 * p := htotal
  have hesum' : e 0 + e 1 = 2 * p := by
    simpa [Finsupp.sum_fintype, Fin.sum_univ_two] using hesum
  have hezero : e 0 = p := by
    have := (hbound e he).1
    have := (hbound e he).2
    omega
  have heone : e 1 = p := by
    have := (hbound e he).1
    have := (hbound e he).2
    omega
  have hecorner : e = bivariateCornerExponent p := by
    apply Finsupp.ext
    intro i
    fin_cases i
    · simpa using hezero
    · simpa using heone
  rw [← hecorner]
  exact MvPolynomial.mem_support_iff.mp he


theorem mem_support_bivariateCornerRemainder
    (Q : BidegreePolynomial ℂ) (p : ℕ) (hbound : BidegreeBound p Q)
    (hrow : ∀ a < p,
      coeff (Finsupp.single 0 a + Finsupp.single 1 p) Q = 0)
    (hcolumn : ∀ b < p,
      coeff (Finsupp.single 0 p + Finsupp.single 1 b) Q = 0)
    {e : Fin 2 →₀ ℕ} (he : e ∈ (bivariateCornerRemainder p Q).support) :
    e ∈ Q.support ∧ e 0 < p ∧ e 1 < p := by
  have hcoeffR : coeff e (bivariateCornerRemainder p Q) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp he
  have hne : e ≠ bivariateCornerExponent p := by
    intro hecorner
    subst e
    exact hcoeffR (coeff_bivariateCornerRemainder_corner p Q)
  have hcoeffQ : coeff e Q ≠ 0 := by
    rw [coeff_bivariateCornerRemainder, if_neg hne] at hcoeffR
    exact hcoeffR
  have heQ : e ∈ Q.support := MvPolynomial.mem_support_iff.mpr hcoeffQ
  have hezero_le := (hbound e heQ).1
  have heone_le := (hbound e heQ).2
  have hezero_lt : e 0 < p := by
    by_contra hnot
    have hezero : e 0 = p := by omega
    by_cases heone : e 1 = p
    · apply hne
      apply Finsupp.ext
      intro i
      fin_cases i
      · simpa using hezero
      · simpa using heone
    · have heone_lt : e 1 < p := by omega
      have hzero := hcolumn (e 1) heone_lt
      apply hcoeffQ
      rw [← hzero]
      congr 1
      apply Finsupp.ext
      intro i
      fin_cases i
      · simpa using hezero
      · simp
  have heone_lt : e 1 < p := by
    by_contra hnot
    have heone : e 1 = p := by omega
    have hzero := hrow (e 0) hezero_lt
    apply hcoeffQ
    rw [← hzero]
    congr 1
    apply Finsupp.ext
    intro i
    fin_cases i
    · simp
    · simpa using heone
  exact ⟨heQ, hezero_lt, heone_lt⟩

 
theorem bidegreeBound_bivariateCornerRemainder
    (Q : BidegreePolynomial ℂ) (p : ℕ) (hp : 0 < p) (hbound : BidegreeBound p Q)
    (hrow : ∀ a < p,
      coeff (Finsupp.single 0 a + Finsupp.single 1 p) Q = 0)
    (hcolumn : ∀ b < p,
      coeff (Finsupp.single 0 p + Finsupp.single 1 b) Q = 0) :
    BidegreeBound (p - 1) (bivariateCornerRemainder p Q) := by
  intro e he
  obtain ⟨_, hezero, heone⟩ :=
    mem_support_bivariateCornerRemainder Q p hbound hrow hcolumn he
  constructor <;> omega


theorem exists_bivariate_corner_normal_form
    (Q : BidegreePolynomial ℂ) (p : ℕ) (hp : 0 < p) (hbound : BidegreeBound p Q)
    (htotal : Q.totalDegree = 2 * p)
    (hrow : ∀ a < p,
      coeff (Finsupp.single 0 a + Finsupp.single 1 p) Q = 0)
    (hcolumn : ∀ b < p,
      coeff (Finsupp.single 0 p + Finsupp.single 1 b) Q = 0) :
    ∃ c : ℂ, ∃ R : BidegreePolynomial ℂ,
      c ≠ 0 ∧ Q = monomial (bivariateCornerExponent p) c + R ∧
        BidegreeBound (p - 1) R := by
  refine ⟨coeff (bivariateCornerExponent p) Q, bivariateCornerRemainder p Q,
    coeff_bivariateCornerExponent_ne_zero Q p hp hbound htotal, ?_,
    bidegreeBound_bivariateCornerRemainder Q p hp hbound hrow hcolumn⟩
  rw [bivariateCornerRemainder]
  abel

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open EuclideanGeometry
open Filter Topology
open scoped Pointwise Real InnerProductSpace EuclideanSpace

variable {n : ℕ}


local notation "o" => (positiveOrientation : Orientation ℝ _root_.Point2 (Fin 2))

 
local notation "J" => Orientation.rightAngleRotation o


lemma directLinearIsometryEquivOfSend_apply_u (u v : _root_.Point2) (hu : u ≠ 0) (huv : ‖u‖ = ‖v‖) :
    directLinearIsometryEquivOfSend u v hu huv u = v := by
  have hv : v ≠ 0 := bundle_Esgk_BridgeIdentity_ne_zero_of_norm_eq hu huv
  set bᵤ : Module.Basis (Fin 2) ℝ _root_.Point2 := o.basisRightAngleRotation u hu with hbu_def
  set bᵥ : Module.Basis (Fin 2) ℝ _root_.Point2 := o.basisRightAngleRotation v hv with hbv_def
   
  change (bᵤ.equiv bᵥ (Equiv.refl (Fin 2))) u = v
  have h0u : bᵤ 0 = u := by rw [hbu_def, o.coe_basisRightAngleRotation u hu]; rfl
  have h0v : bᵥ 0 = v := by rw [hbv_def, o.coe_basisRightAngleRotation v hv]; rfl
   
  have happ : (bᵤ.equiv bᵥ (Equiv.refl (Fin 2))) (bᵤ 0) = bᵥ 0 := by
    rw [Module.Basis.equiv_apply, Equiv.refl_apply]
   
  rw [← h0u, happ, h0v]


lemma directAffineIsometryEquivOfSendPair_apply_a (a b c d : _root_.Point2) (hab : a ≠ b) (hdist : dist a b = dist c d) :
    directAffineIsometryEquivOfSendPair a b c d hab hdist a = c := by
  unfold directAffineIsometryEquivOfSendPair
  simp

 
lemma directAffineIsometryEquivOfSendPair_apply_b (a b c d : _root_.Point2) (hab : a ≠ b) (hdist : dist a b = dist c d) :
    directAffineIsometryEquivOfSendPair a b c d hab hdist b = d := by
  unfold directAffineIsometryEquivOfSendPair
  change directLinearIsometryEquivOfSend (b - a) (d - c) _ _ (b - a) + c = d
  rw [directLinearIsometryEquivOfSend_apply_u]
  abel


end Esgk

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

variable {F L₁ L₂ K : Type*}
variable [Field F] [Field L₁] [Field L₂] [Field K]
variable [Algebra F L₁] [Algebra F L₂] [Algebra F K]


@[simp]
theorem commonImageFunctionFieldAutomorphismOfSourceEquiv_apply_second
    (φ₁ : L₁ →ₐ[F] K)
    (φ₂ : L₂ →ₐ[F] K)
    (e : L₁ ≃ₐ[F] L₂)
    (hφ₁ : Function.Surjective φ₁)
    (hφ₂ : Function.Surjective φ₂)
    (x : L₁) :
    commonImageFunctionFieldAutomorphismOfSourceEquiv φ₁ φ₂ e hφ₁ hφ₂ (φ₂ (e x)) =
      φ₁ x := by
  exact commonImageFunctionFieldAutomorphism_apply_second φ₁ (φ₂.comp e.toAlgHom) hφ₁
    (hφ₂.comp e.surjective) x


theorem commonImageFunctionFieldAutomorphismOfSourceEquiv_apply_pair
    (φ₁ : L₁ →ₐ[F] K)
    (φ₂ : L₂ →ₐ[F] K)
    (e : L₁ ≃ₐ[F] L₂)
    (hφ₁ : Function.Surjective φ₁)
    (hφ₂ : Function.Surjective φ₂)
    (u v : L₁) :
    commonImageFunctionFieldAutomorphismOfSourceEquiv φ₁ φ₂ e hφ₁ hφ₂ (φ₂ (e u)) =
        φ₁ u ∧
      commonImageFunctionFieldAutomorphismOfSourceEquiv φ₁ φ₂ e hφ₁ hφ₂ (φ₂ (e v)) =
        φ₁ v :=
  ⟨commonImageFunctionFieldAutomorphismOfSourceEquiv_apply_second φ₁ φ₂ e hφ₁ hφ₂ u,
    commonImageFunctionFieldAutomorphismOfSourceEquiv_apply_second φ₁ φ₂ e hφ₁ hφ₂ v⟩


theorem exists_commonImageFunctionFieldAutomorphism_of_sourceEquiv
    (φ₁ : L₁ →ₐ[F] K)
    (φ₂ : L₂ →ₐ[F] K)
    (e : L₁ ≃ₐ[F] L₂)
    (hφ₁ : Function.Surjective φ₁)
    (hφ₂ : Function.Surjective φ₂)
    (u v : L₁) :
    ∃ T : K ≃ₐ[F] K,
      T (φ₂ (e u)) = φ₁ u ∧ T (φ₂ (e v)) = φ₁ v :=
  ⟨commonImageFunctionFieldAutomorphismOfSourceEquiv φ₁ φ₂ e hφ₁ hφ₂,
    commonImageFunctionFieldAutomorphismOfSourceEquiv_apply_pair φ₁ φ₂ e hφ₁ hφ₂ u v⟩

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

namespace IrreduciblePlanePolynomial

variable {F : Type*} [Field F]


theorem isIntegral_algEquiv_apply_of_finite_generator_range
    (C : IrreduciblePlanePolynomial F)
    (e : C.FunctionField ≃ₐ[F] C.FunctionField)
    (u : Fin 2 → C.CoordinateRing)
    (hu : Algebra.adjoin F (Set.range u) = ⊤)
    (he : ∀ i, IsIntegral C.CoordinateRing
      (e (algebraMap C.CoordinateRing C.FunctionField (u i)))) :
    ∀ a : C.CoordinateRing,
      IsIntegral C.CoordinateRing
        (e (algebraMap C.CoordinateRing C.FunctionField a)) := by
  let g : C.CoordinateRing →ₐ[F] C.FunctionField :=
    e.toAlgHom.comp
      (IsScalarTower.toAlgHom F C.CoordinateRing C.FunctionField)
  let S : Subalgebra C.CoordinateRing C.FunctionField :=
    Algebra.adjoin C.CoordinateRing (g '' Set.range u)
  have hgen : ∀ z ∈ g '' Set.range u,
      IsIntegral C.CoordinateRing z := by
    intro z hz
    rcases hz with ⟨a, ⟨i, rfl⟩, rfl⟩
    simpa [g] using he i
  have hfg : S.toSubmodule.FG := by
    exact fg_adjoin_of_finite
      (Set.Finite.image g (Set.finite_range u)) hgen
  have hgmem : ∀ a : C.CoordinateRing, g a ∈ S := by
    intro a
    have ha : a ∈ Algebra.adjoin F (Set.range u) := by
      rw [hu]
      trivial
    induction ha using Algebra.adjoin_induction with
    | mem z hz =>
        exact Algebra.subset_adjoin ⟨z, hz, rfl⟩
    | algebraMap r =>
        rw [g.commutes r,
          IsScalarTower.algebraMap_apply F
            C.CoordinateRing C.FunctionField]
        exact S.algebraMap_mem _
    | add x y hx hy h₁ h₂ =>
        rw [map_add]
        exact S.add_mem h₁ h₂
    | mul x y hx hy h₁ h₂ =>
        rw [map_mul]
        exact S.mul_mem h₁ h₂
  intro a
  have h := IsIntegral.of_mem_of_fg S hfg (g a) (hgmem a)
  simpa [g] using h


end IrreduciblePlanePolynomial

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

namespace IrreduciblePlanePolynomial

variable {F : Type*} [Field F]


@[simp]
theorem squaredDistanceOutputClass_zero
    (C : IrreduciblePlanePolynomial F) (r : F) :
    C.squaredDistanceOutputClass r 0 = C.leftSquaredDistanceClass r := by
  simp [squaredDistanceOutputClass]

 
@[simp]
theorem squaredDistanceOutputClass_one
    (C : IrreduciblePlanePolynomial F) (r : F) :
    C.squaredDistanceOutputClass r 1 = C.rightSquaredDistanceClass r := by
  simp [squaredDistanceOutputClass]


@[simp]
theorem distancePairAlgHom_apply_X
    (C : IrreduciblePlanePolynomial F) (r : F) (i : Fin 2) :
    C.distancePairAlgHom r (MvPolynomial.X i) =
      C.squaredDistanceOutputClass r i := by
  simp [distancePairAlgHom]


@[simp]
theorem distanceImageCoordinateRingHom_apply_coordinate
    (C : IrreduciblePlanePolynomial F) (r : F) (i : Fin 2) :
    C.distanceImageCoordinateRingHom r (C.distanceImageCoordinateClass r i) =
      C.squaredDistanceOutputClass r i := by
  change
    Ideal.kerLiftAlg (C.distancePairAlgHom r)
        (Ideal.Quotient.mk (RingHom.ker (C.distancePairAlgHom r))
          (MvPolynomial.X i)) =
      C.squaredDistanceOutputClass r i
  rw [Ideal.kerLiftAlg_mk, C.distancePairAlgHom_apply_X]


@[simp]
theorem distanceImageFunctionFieldHom_apply_coordinate
    (C : IrreduciblePlanePolynomial F) (r : F) (i : Fin 2) :
    C.distanceImageFunctionFieldHom r (C.distanceImageCoordinate r i) =
      algebraMap C.CoordinateRing C.FunctionField
        (C.squaredDistanceOutputClass r i) := by
  simp [distanceImageFunctionFieldHom, distanceImageCoordinate,
    distanceImageCoordinateRingToFunctionField]


@[simp]
theorem distanceImageFunctionFieldHom_apply_coordinate_zero
    (C : IrreduciblePlanePolynomial F) (r : F) :
    C.distanceImageFunctionFieldHom r (C.distanceImageCoordinate r 0) =
      (C.coordinate 0 + algebraMap F C.FunctionField r) ^ 2 +
        C.coordinate 1 ^ 2 := by
  simp [leftSquaredDistanceClass, coordinate,
    IsScalarTower.algebraMap_apply F C.CoordinateRing C.FunctionField]


@[simp]
theorem distanceImageFunctionFieldHom_apply_coordinate_one
    (C : IrreduciblePlanePolynomial F) (r : F) :
    C.distanceImageFunctionFieldHom r (C.distanceImageCoordinate r 1) =
      (C.coordinate 0 - algebraMap F C.FunctionField r) ^ 2 +
        C.coordinate 1 ^ 2 := by
  simp [rightSquaredDistanceClass, coordinate,
    IsScalarTower.algebraMap_apply F C.CoordinateRing C.FunctionField]


theorem distanceImageFunctionFieldHom_apply_coordinates
    (C : IrreduciblePlanePolynomial F) (r : F) :
    C.distanceImageFunctionFieldHom r (C.distanceImageCoordinate r 0) =
        (C.coordinate 0 + algebraMap F C.FunctionField r) ^ 2 +
          C.coordinate 1 ^ 2 ∧
      C.distanceImageFunctionFieldHom r (C.distanceImageCoordinate r 1) =
        (C.coordinate 0 - algebraMap F C.FunctionField r) ^ 2 +
          C.coordinate 1 ^ 2 :=
  ⟨C.distanceImageFunctionFieldHom_apply_coordinate_zero r,
    C.distanceImageFunctionFieldHom_apply_coordinate_one r⟩


end IrreduciblePlanePolynomial

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

namespace IrreduciblePlanePolynomial

variable {F : Type*} [Field F]


@[simp]
theorem coordinateRingAlgEquivTransport_apply_mk
    (C : IrreduciblePlanePolynomial F)
    (e : MvPolynomial (Fin 2) F ≃ₐ[F] MvPolynomial (Fin 2) F)
    (p : MvPolynomial (Fin 2) F) :
    C.coordinateRingAlgEquivTransport e
        (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (e p) :=
  rfl


@[simp]
theorem functionFieldAlgEquivTransport_apply_algebraMap
    (C : IrreduciblePlanePolynomial F)
    (e : MvPolynomial (Fin 2) F ≃ₐ[F] MvPolynomial (Fin 2) F)
    (a : C.CoordinateRing) :
    C.functionFieldAlgEquivTransport e
        (algebraMap C.CoordinateRing C.FunctionField a) =
      algebraMap (C.transportByAlgEquiv e).CoordinateRing
        (C.transportByAlgEquiv e).FunctionField
        (C.coordinateRingAlgEquivTransport e a) := by
  exact IsFractionRing.algEquivOfAlgEquiv_algebraMap
    (C.coordinateRingAlgEquivTransport e) a

@[simp]
theorem functionFieldAlgEquivTransport_symm_apply_algebraMap
    (C : IrreduciblePlanePolynomial F)
    (e : MvPolynomial (Fin 2) F ≃ₐ[F] MvPolynomial (Fin 2) F)
    (a : (C.transportByAlgEquiv e).CoordinateRing) :
    (C.functionFieldAlgEquivTransport e).symm
        (algebraMap (C.transportByAlgEquiv e).CoordinateRing
          (C.transportByAlgEquiv e).FunctionField a) =
      algebraMap C.CoordinateRing C.FunctionField
        ((C.coordinateRingAlgEquivTransport e).symm a) := by
  exact IsFractionRing.algEquivOfAlgEquiv_algebraMap
    (C.coordinateRingAlgEquivTransport e).symm a


end IrreduciblePlanePolynomial

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open scoped BigOperators

namespace Esgk

lemma fin_sum_val_add (a b : ℕ) :
    (∑ i : Fin (a + b), (i : ℕ)) =
      (∑ i : Fin a, (i : ℕ)) + (∑ i : Fin b, (i : ℕ)) + a * b := by
  rw [Fin.sum_univ_add]
  simp_rw [Fin.val_castAdd, Fin.val_natAdd, Nat.add_comm a]
  rw [Finset.sum_add_distrib]
  simp [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm]

lemma sylvester_selected_index_sum {m n : ℕ} (σ : Fin (m + n) → Fin (m + n))
    (hσ : Function.Bijective σ)
    (hl : ∀ i : Fin m, i.val ≤ (σ (Fin.castAdd n i)).val ∧
      (σ (Fin.castAdd n i)).val ≤ i.val + n)
    (hr : ∀ j : Fin n, j.val ≤ (σ (Fin.natAdd m j)).val ∧
      (σ (Fin.natAdd m j)).val ≤ j.val + m) :
    (∑ i : Fin m, ((σ (Fin.castAdd n i)).val - i.val)) +
      (∑ j : Fin n, ((σ (Fin.natAdd m j)).val - j.val)) = m * n := by
  have hsigma : (∑ x : Fin (m + n), (σ x).val) = ∑ x : Fin (m + n), x.val := by
    let e : Fin (m + n) ≃ Fin (m + n) := Equiv.ofBijective σ hσ
    simpa [e] using (e.sum_comp (fun x : Fin (m + n) => x.val))
  have hleft := Finset.sum_tsub_distrib (s := (Finset.univ : Finset (Fin m)))
    (f := fun i : Fin m => (σ (Fin.castAdd n i)).val) (g := fun i => i.val)
    (fun i _ => (hl i).1)
  have hright := Finset.sum_tsub_distrib (s := (Finset.univ : Finset (Fin n)))
    (f := fun j : Fin n => (σ (Fin.natAdd m j)).val) (g := fun j => j.val)
    (fun j _ => (hr j).1)
  rw [hleft, hright]
  have hAB : (∑ i : Fin m, i.val) ≤ ∑ i : Fin m, (σ (Fin.castAdd n i)).val :=
    Finset.sum_le_sum (fun i _ => (hl i).1)
  have hCD : (∑ j : Fin n, j.val) ≤ ∑ j : Fin n, (σ (Fin.natAdd m j)).val :=
    Finset.sum_le_sum (fun j _ => (hr j).1)
  have hcombine :
      (∑ i : Fin m, (σ (Fin.castAdd n i)).val) - ∑ i : Fin m, i.val +
        ((∑ j : Fin n, (σ (Fin.natAdd m j)).val) - ∑ j : Fin n, j.val) =
        ((∑ i : Fin m, (σ (Fin.castAdd n i)).val) +
          ∑ j : Fin n, (σ (Fin.natAdd m j)).val) -
        ((∑ i : Fin m, i.val) + ∑ j : Fin n, j.val) := by omega
  rw [hcombine]
  rw [← Fin.sum_univ_add (fun x : Fin (m + n) => (σ x).val)]
  rw [hsigma]
  rw [fin_sum_val_add]
  omega

lemma nat_sub_add_sub_le {a b c x y : ℕ} (hx : x ≤ a) (hy : y ≤ b) (hxy : x + y = c) :
    a - x + (b - y) ≤ a + b - c := by omega


theorem headResultant_totalDegree_le_weighted {n : ℕ}
    (p q : MvPolynomial (Fin (n + 1)) ℝ) (d₁ d₂ : ℕ)
    (hpHead : (headCurry p).natDegree ≤ d₁)
    (hqHead : (headCurry q).natDegree ≤ d₂)
    (hp : ∀ k, ((headCurry p).coeff k).totalDegree ≤ d₁ - k)
    (hq : ∀ k, ((headCurry q).coeff k).totalDegree ≤ d₂ - k) :
    (headResultant p q).totalDegree ≤
      (headCurry q).natDegree * d₁ + (headCurry p).natDegree * d₂ -
        (headCurry p).natDegree * (headCurry q).natDegree := by
  classical
  rw [headResultant, Polynomial.resultant, Matrix.det_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro σ hσ
  by_cases hterm : ∏ i : Fin ((headCurry p).natDegree + (headCurry q).natDegree),
      Polynomial.sylvester (headCurry p) (headCurry q)
        (headCurry p).natDegree (headCurry q).natDegree (σ i) i = 0
  · rw [hterm]
    change 0 ≤ _
    omega
  · apply (MvPolynomial.totalDegree_smul_le _ _).trans
    apply (MvPolynomial.totalDegree_finsetProd _ _).trans
    rw [Fin.sum_univ_add]
    let m := (headCurry p).natDegree
    let k := (headCurry q).natDegree
    have hprod (i : Fin (m + k)) :
        Polynomial.sylvester (headCurry p) (headCurry q) m k (σ i) i ≠ 0 := by
      exact (Finset.prod_ne_zero_iff.mp hterm) i (Finset.mem_univ i)
    have hl (i : Fin m) :
        i.val ≤ (σ (Fin.castAdd k i)).val ∧
          (σ (Fin.castAdd k i)).val ≤ i.val + k := by
      have hi := hprod (Fin.castAdd k i)
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left] at hi
      split_ifs at hi with h
      · exact h
      · simp_all
    have hr (j : Fin k) :
        j.val ≤ (σ (Fin.natAdd m j)).val ∧
          (σ (Fin.natAdd m j)).val ≤ j.val + m := by
      have hi := hprod (Fin.natAdd m j)
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right] at hi
      split_ifs at hi with h
      · exact h
      · simp_all
    have hsel := sylvester_selected_index_sum σ σ.bijective hl hr
    have hleft : ∀ i : Fin m,
        (Polynomial.sylvester (headCurry p) (headCurry q) m k
          (σ (Fin.castAdd k i)) (Fin.castAdd k i)).totalDegree ≤
          d₂ - ((σ (Fin.castAdd k i)).val - i.val) := by
      intro i
      have hi := hprod (Fin.castAdd k i)
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left] at hi ⊢
      split_ifs with h
      · exact hq _
      · simp_all
    have hright : ∀ j : Fin k,
        (Polynomial.sylvester (headCurry p) (headCurry q) m k
          (σ (Fin.natAdd m j)) (Fin.natAdd m j)).totalDegree ≤
          d₁ - ((σ (Fin.natAdd m j)).val - j.val) := by
      intro j
      have hj := hprod (Fin.natAdd m j)
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right] at hj ⊢
      split_ifs with h
      · exact hp _
      · simp_all
    apply Nat.le_trans (Nat.add_le_add
      (Finset.sum_le_sum fun i _ => hleft i)
      (Finset.sum_le_sum fun j _ => hright j))
    have hqidx : ∀ i : Fin m, (σ (Fin.castAdd k i)).val - i.val ≤ d₂ := by
      intro i
      have hc : (headCurry q).coeff ((σ (Fin.castAdd k i)).val - i.val) ≠ 0 := by
        have hi := hprod (Fin.castAdd k i)
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left] at hi
        split_ifs at hi with h
        · exact hi
        · simp at hi
      exact (Polynomial.le_natDegree_of_ne_zero hc).trans hqHead
    have hpidx : ∀ j : Fin k, (σ (Fin.natAdd m j)).val - j.val ≤ d₁ := by
      intro j
      have hc : (headCurry p).coeff ((σ (Fin.natAdd m j)).val - j.val) ≠ 0 := by
        have hj := hprod (Fin.natAdd m j)
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right] at hj
        split_ifs at hj with h
        · exact hj
        · simp at hj
      exact (Polynomial.le_natDegree_of_ne_zero hc).trans hpHead
    rw [Finset.sum_tsub_distrib _ (fun i _ => hqidx i)]
    rw [Finset.sum_tsub_distrib _ (fun j _ => hpidx j)]
    have hc : (∑ _ : Fin m, d₂) = m * d₂ := by simp
    have hc' : (∑ _ : Fin k, d₁) = k * d₁ := by simp
    rw [hc, hc']
    have hQ : (∑ i : Fin m, ((σ (Fin.castAdd k i)).val - (i : ℕ))) ≤ m * d₂ := by
      calc
        (∑ i : Fin m, ((σ (Fin.castAdd k i)).val - (i : ℕ))) ≤ ∑ _ : Fin m, d₂ :=
          Finset.sum_le_sum fun i _ => hqidx i
        _ = m * d₂ := hc
    have hP : (∑ j : Fin k, ((σ (Fin.natAdd m j)).val - (j : ℕ))) ≤ k * d₁ := by
      calc
        (∑ j : Fin k, ((σ (Fin.natAdd m j)).val - (j : ℕ))) ≤ ∑ _ : Fin k, d₁ :=
          Finset.sum_le_sum fun j _ => hpidx j
        _ = k * d₁ := hc'
    have hsel' :
        (∑ i : Fin m, ((σ (Fin.castAdd k i)).val - (i : ℕ))) +
            (∑ j : Fin k, ((σ (Fin.natAdd m j)).val - (j : ℕ))) = m * k := by
      change (∑ i : Fin m, ((σ (Fin.castAdd k i)).val - (i : ℕ))) +
          (∑ j : Fin k, ((σ (Fin.natAdd m j)).val - (j : ℕ))) = m * k at hsel
      exact hsel
    rw [Nat.add_comm ((headCurry q).natDegree * d₁) ((headCurry p).natDegree * d₂)]
    exact nat_sub_add_sub_le hQ hP hsel'

theorem headResultant_totalDegree_le_weighted_mul {n : ℕ}
    (p q : MvPolynomial (Fin (n + 1)) ℝ) (d₁ d₂ : ℕ)
    (hpHead : (headCurry p).natDegree ≤ d₁)
    (hqHead : (headCurry q).natDegree ≤ d₂)
    (hp : ∀ k, ((headCurry p).coeff k).totalDegree ≤ d₁ - k)
    (hq : ∀ k, ((headCurry q).coeff k).totalDegree ≤ d₂ - k) :
    (headResultant p q).totalDegree ≤ d₁ * d₂ := by
  apply (headResultant_totalDegree_le_weighted p q d₁ d₂ hpHead hqHead hp hq).trans
  let m := (headCurry p).natDegree
  let k := (headCurry q).natDegree
  have hmk : m * k ≤ k * d₁ := by
    simpa [m, k, Nat.mul_comm] using Nat.mul_le_mul_left k hpHead
  have hsplit : k * d₁ + m * d₂ - m * k = m * d₂ + (k * d₁ - m * k) := by
    rw [Nat.add_comm (k * d₁) (m * d₂), Nat.add_sub_assoc hmk]
  have hdiff : k * d₁ - m * k ≤ d₂ * (d₁ - m) := by
    calc
      k * d₁ - m * k = (d₁ - m) * k := by
        rw [Nat.mul_sub_right_distrib]
        ac_rfl
      _ ≤ d₂ * (d₁ - m) := by
        simpa [m, k, Nat.mul_comm] using Nat.mul_le_mul_right (d₁ - m) hqHead
  have hsplit_le : m * d₂ + (k * d₁ - m * k) ≤ d₁ * d₂ := by
    calc
      m * d₂ + (k * d₁ - m * k) ≤ m * d₂ + d₂ * (d₁ - m) :=
        Nat.add_le_add_left hdiff _
      _ = d₁ * d₂ := by
        have hd : m + (d₁ - m) = d₁ := Nat.add_sub_of_le hpHead
        rw [show m * d₂ = d₂ * m by ac_rfl]
        rw [← Nat.mul_add, hd]
        ac_rfl
  rw [show (headCurry q).natDegree * d₁ + (headCurry p).natDegree * d₂ -
      (headCurry p).natDegree * (headCurry q).natDegree =
      m * d₂ + (k * d₁ - m * k) by simpa [m, k] using hsplit]
  exact hsplit_le

theorem headResultant_totalDegree_le_totalDegree_mul {n : ℕ}
    (p q : MvPolynomial (Fin (n + 1)) ℝ) :
    (headResultant p q).totalDegree ≤ p.totalDegree * q.totalDegree := by
  have hpHead : (headCurry p).natDegree ≤ p.totalDegree := by
    change (MvPolynomial.finSuccEquiv ℝ n p).natDegree ≤ p.totalDegree
    rw [MvPolynomial.natDegree_finSuccEquiv]
    exact MvPolynomial.degreeOf_le_totalDegree p 0
  have hqHead : (headCurry q).natDegree ≤ q.totalDegree := by
    change (MvPolynomial.finSuccEquiv ℝ n q).natDegree ≤ q.totalDegree
    rw [MvPolynomial.natDegree_finSuccEquiv]
    exact MvPolynomial.degreeOf_le_totalDegree q 0
  have hp : ∀ k, ((headCurry p).coeff k).totalDegree ≤ p.totalDegree - k := by
    intro k
    change ((MvPolynomial.finSuccEquiv ℝ n p).coeff k).totalDegree ≤ p.totalDegree - k
    by_cases hk : (MvPolynomial.finSuccEquiv ℝ n p).coeff k = 0
    · simp [hk]
    · have hdegree := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le p k hk
      omega
  have hq : ∀ k, ((headCurry q).coeff k).totalDegree ≤ q.totalDegree - k := by
    intro k
    change ((MvPolynomial.finSuccEquiv ℝ n q).coeff k).totalDegree ≤ q.totalDegree - k
    by_cases hk : (MvPolynomial.finSuccEquiv ℝ n q).coeff k = 0
    · simp [hk]
    · have hdegree := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le q k hk
      omega
  exact headResultant_totalDegree_le_weighted_mul p q p.totalDegree q.totalDegree
    hpHead hqHead hp hq

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic


@[simp]
theorem eval_planeAffinePolynomialEquiv
    (g : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) (p : PlanePoly) (z : PachDeZeeuw.Algebraic.Point2) :
    MvPolynomial.eval (fun i ↦ z i) (planeAffinePolynomialEquiv g p) =
      MvPolynomial.eval (fun i ↦ g z i) p := by
  exact eval_planeAffinePolynomialHom g p z

end Esgk
end

end


section
set_option autoImplicit true

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


set_option linter.style.longLine false

namespace PachDeZeeuw

open EuclideanGeometry


lemma ParallelLinePair.left_controlledDegenerate {C₁ C₂ : Set Point2}
    (h : ParallelLinePair C₁ C₂) : PlaneCurve.IsLineOrCircle C₁ := by
  rcases h with ⟨a, b, c₁, c₂, hab, rfl, rfl⟩
  exact Or.inl ⟨a, b, c₁, hab, rfl⟩


lemma OrthogonalLinePair.left_controlledDegenerate {C₁ C₂ : Set Point2}
    (h : OrthogonalLinePair C₁ C₂) : PlaneCurve.IsLineOrCircle C₁ := by
  rcases h with ⟨a₁, b₁, c₁, a₂, b₂, c₂, hab₁, hab₂, _horth, rfl, rfl⟩
  exact Or.inl ⟨a₁, b₁, c₁, hab₁, rfl⟩


lemma ConcentricCirclePair.left_controlledDegenerate {C₁ C₂ : Set Point2}
    (h : ConcentricCirclePair C₁ C₂) : PlaneCurve.IsLineOrCircle C₁ := by
  rcases h with ⟨center, r₁, r₂, rfl, rfl⟩
  exact Or.inr ⟨center, r₁, rfl⟩


lemma ExceptionalCurvePair.left_controlledDegenerate {C₁ C₂ : Set Point2}
    (h : ExceptionalCurvePair C₁ C₂) : PlaneCurve.IsLineOrCircle C₁ := by
  rcases h with h | h | h
  · exact ParallelLinePair.left_controlledDegenerate h
  · exact OrthogonalLinePair.left_controlledDegenerate h
  · exact ConcentricCirclePair.left_controlledDegenerate h


lemma assumption31Data_of_not_controlledDegenerate {C₁ C₂ : Set Point2}
    {P₁ P₂ : Finset Point2}
    (h₁ : ¬ PlaneCurve.IsLineOrCircle C₁)
    (h₂ : ¬ PlaneCurve.IsLineOrCircle C₂)
    (hdisj : Disjoint (P₁ : Set Point2) (P₂ : Set Point2))
    (hexc : ¬ ExceptionalCurvePair C₁ C₂) :
    Assumption31Data C₁ C₂ P₁ P₂ where
  noVerticalComponent₁ := by
    rintro ⟨c, hc⟩
    exact h₁ (Or.inl ⟨1, 0, c, by simp, by rw [hc]; ext p; simp⟩)
  noVerticalComponent₂ := by
    rintro ⟨c, hc⟩
    exact h₂ (Or.inl ⟨1, 0, c, by simp, by rw [hc]; ext p; simp⟩)
  pointSetsDisjoint := hdisj
  circleCenterNotInPointSet :=
    ⟨fun center r hsphere => absurd (Or.inr ⟨center, r, hsphere⟩) h₁,
     fun center r hsphere => absurd (Or.inr ⟨center, r, hsphere⟩) h₂⟩
  sparseConcentricFibers :=
    ⟨fun center r hsphere => absurd (Or.inr ⟨center, r, hsphere⟩) h₁,
     fun center r hsphere => absurd (Or.inr ⟨center, r, hsphere⟩) h₂⟩
  sparseParallelFibers :=
    ⟨fun a b c hab hline => absurd (Or.inl ⟨a, b, c, hab, hline⟩) h₁,
     fun a b c hab hline => absurd (Or.inl ⟨a, b, c, hab, hline⟩) h₂⟩
  sparseOrthogonalFibers :=
    ⟨fun a b c hab hline => absurd (Or.inl ⟨a, b, c, hab, hline⟩) h₁,
     fun a b c hab hline => absurd (Or.inl ⟨a, b, c, hab, hline⟩) h₂⟩
  noExceptionalPair := hexc


end PachDeZeeuw

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

namespace IrreduciblePlanePolynomial


@[simp]
theorem eval_affineIsometryTransport_polynomial
    (C : IrreduciblePlanePolynomial ℝ)
    (g : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) (z : PachDeZeeuw.Algebraic.Point2) :
    MvPolynomial.eval (fun i ↦ z i)
        (C.affineIsometryTransport g).polynomial =
      MvPolynomial.eval (fun i ↦ g.symm z i) C.polynomial := by
  exact eval_planeAffinePolynomialEquiv g.symm C.polynomial z


theorem mem_zeroSet_affineIsometryTransport_iff
    (C : IrreduciblePlanePolynomial ℝ)
    (g : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) (z : PachDeZeeuw.Algebraic.Point2) :
    z ∈ PlaneCurveZeroSet (C.affineIsometryTransport g).polynomial ↔
      g.symm z ∈ PlaneCurveZeroSet C.polynomial := by
  change
    MvPolynomial.eval (fun i ↦ z i)
          (C.affineIsometryTransport g).polynomial = 0 ↔
      MvPolynomial.eval (fun i ↦ g.symm z i) C.polynomial = 0
  rw [C.eval_affineIsometryTransport_polynomial]


theorem affineIsometry_image_zeroSet_eq
    (C : IrreduciblePlanePolynomial ℝ)
    (g : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) :
    g '' PlaneCurveZeroSet C.polynomial =
      PlaneCurveZeroSet (C.affineIsometryTransport g).polynomial := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [C.mem_zeroSet_affineIsometryTransport_iff]
    simpa using hx
  · intro hz
    refine ⟨g.symm z, ?_, by simp⟩
    exact (C.mem_zeroSet_affineIsometryTransport_iff g z).mp hz


end IrreduciblePlanePolynomial

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

namespace IrreduciblePlanePolynomial

variable {F : Type*} [Field F]


@[simp]
theorem affineNormalizationRingAlgEquivOfFunctionFieldAlgEquiv_apply
    (C : IrreduciblePlanePolynomial F)
    (e : C.FunctionField ≃ₐ[F] C.FunctionField)
    (hforward : ∀ a : C.CoordinateRing,
      IsIntegral C.CoordinateRing
        (e (algebraMap C.CoordinateRing C.FunctionField a)))
    (hbackward : ∀ a : C.CoordinateRing,
      IsIntegral C.CoordinateRing
        (e.symm (algebraMap C.CoordinateRing C.FunctionField a)))
    (x : C.affineNormalizationRing) :
    ((C.affineNormalizationRingAlgEquivOfFunctionFieldAlgEquiv
      e hforward hbackward x : C.affineNormalizationRing) :
      C.FunctionField) = e (x : C.FunctionField) :=
  rfl

@[simp]
theorem affineNormalizationRingAlgEquivOfFunctionFieldAlgEquiv_symm_apply
    (C : IrreduciblePlanePolynomial F)
    (e : C.FunctionField ≃ₐ[F] C.FunctionField)
    (hforward : ∀ a : C.CoordinateRing,
      IsIntegral C.CoordinateRing
        (e (algebraMap C.CoordinateRing C.FunctionField a)))
    (hbackward : ∀ a : C.CoordinateRing,
      IsIntegral C.CoordinateRing
        (e.symm (algebraMap C.CoordinateRing C.FunctionField a)))
    (x : C.affineNormalizationRing) :
    (((C.affineNormalizationRingAlgEquivOfFunctionFieldAlgEquiv
      e hforward hbackward).symm x : C.affineNormalizationRing) :
      C.FunctionField) = e.symm (x : C.FunctionField) :=
  rfl

end IrreduciblePlanePolynomial

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

namespace IrreduciblePlanePolynomial

variable {F : Type*} [Field F]


@[simp]
theorem distanceImageCoordinateRingAlgEquivOfIdealEq_apply_coordinate
    (C₁ C₂ : IrreduciblePlanePolynomial F) (r₁ r₂ : F)
    (hIdeal : C₁.distanceImageIdeal r₁ = C₂.distanceImageIdeal r₂)
    (i : Fin 2) :
    distanceImageCoordinateRingAlgEquivOfIdealEq C₁ C₂ r₁ r₂ hIdeal
        (C₁.distanceImageCoordinateClass r₁ i) =
      C₂.distanceImageCoordinateClass r₂ i := by
  exact Ideal.quotientEquivAlgOfEq_mk F hIdeal (MvPolynomial.X i)


@[simp]
theorem distanceImageFunctionFieldAlgEquivOfIdealEq_apply_coordinate
    (C₁ C₂ : IrreduciblePlanePolynomial F) (r₁ r₂ : F)
    (hIdeal : C₁.distanceImageIdeal r₁ = C₂.distanceImageIdeal r₂)
    (i : Fin 2) :
    distanceImageFunctionFieldAlgEquivOfIdealEq C₁ C₂ r₁ r₂ hIdeal
        (C₁.distanceImageCoordinate r₁ i) =
      C₂.distanceImageCoordinate r₂ i := by
  simp [distanceImageFunctionFieldAlgEquivOfIdealEq, distanceImageCoordinate]


end IrreduciblePlanePolynomial

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

namespace IrreduciblePlanePolynomial

variable {F : Type*} [Field F]


theorem mk_normalizedLeftSquaredDistancePolynomial
    (C : IrreduciblePlanePolynomial F) (r : F) :
    Ideal.Quotient.mk
        (Ideal.span ({C.polynomial} : Set (MvPolynomial (Fin 2) F)))
        (normalizedLeftSquaredDistancePolynomial r) =
      C.leftSquaredDistanceClass r := by
  have hC :
      Ideal.Quotient.mk
          (Ideal.span ({C.polynomial} : Set (MvPolynomial (Fin 2) F)))
          (MvPolynomial.C r) =
        algebraMap F C.CoordinateRing r := by
    rw [← Ideal.Quotient.mk_algebraMap]
    exact congrArg _
      (DFunLike.congr_fun (MvPolynomial.algebraMap_eq F (Fin 2)) r).symm
  simp only [normalizedLeftSquaredDistancePolynomial, leftSquaredDistanceClass,
    coordinateClass, map_add, map_pow]
  rw [hC]

 
theorem mk_normalizedRightSquaredDistancePolynomial
    (C : IrreduciblePlanePolynomial F) (r : F) :
    Ideal.Quotient.mk
        (Ideal.span ({C.polynomial} : Set (MvPolynomial (Fin 2) F)))
        (normalizedRightSquaredDistancePolynomial r) =
      C.rightSquaredDistanceClass r := by
  have hC :
      Ideal.Quotient.mk
          (Ideal.span ({C.polynomial} : Set (MvPolynomial (Fin 2) F)))
          (MvPolynomial.C r) =
        algebraMap F C.CoordinateRing r := by
    rw [← Ideal.Quotient.mk_algebraMap]
    exact congrArg _
      (DFunLike.congr_fun (MvPolynomial.algebraMap_eq F (Fin 2)) r).symm
  simp only [normalizedRightSquaredDistancePolynomial, rightSquaredDistanceClass,
    coordinateClass, map_add, map_sub, map_pow]
  rw [hC]


namespace NormalizedDistancePairPrimeComponent

variable {C₁ C₂ : IrreduciblePlanePolynomial F} {r₁ r₂ : F}


end NormalizedDistancePairPrimeComponent


end IrreduciblePlanePolynomial

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk


@[simp]
theorem planeIsotropicCoordinateEquiv_symm_apply (p : ComplexPlanePoly) :
    planeIsotropicCoordinateEquiv.symm p = isotropicToPlaneCoordinates p :=
  rfl


@[simp]
theorem isotropicTranslationEquiv_apply (ξ : ℂ) (p : ComplexPlanePoly) :
    isotropicTranslationEquiv ξ p = isotropicTranslation ξ p :=
  rfl

@[simp]
theorem isotropicTranslationEquiv_symm_apply (ξ : ℂ) (p : ComplexPlanePoly) :
    (isotropicTranslationEquiv ξ).symm p = inverseIsotropicTranslation ξ p :=
  rfl

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open EuclideanGeometry
open scoped EuclideanGeometry


theorem exists_normalizing_isometry_twoAnchor_fiber_dichotomy
    {a c x y : _root_.Point2} (hac : a ≠ c)
    (ha : dist x a ^ 2 = dist y a ^ 2)
    (hc : dist x c ^ 2 = dist y c ^ 2) :
    ∃ (g : _root_.Point2 ≃ᵃⁱ[ℝ] _root_.Point2) (r : ℝ),
      0 < r ∧ g a = xAxisPoint (-r) ∧ g c = xAxisPoint r ∧
        (x = y ∨ ((g x) 0 = (g y) 0 ∧ (g x) 1 = -(g y) 1)) := by
  let r : ℝ := dist a c / 2
  have hr : 0 < r := by
    dsimp [r]
    have hdist : 0 < dist a c := dist_pos.mpr hac
    positivity
  have htarget : dist a c = dist (xAxisPoint (-r)) (xAxisPoint r) := by
    rw [dist_xAxisPoint_neg_eq r hr.le]
    dsimp [r]
    ring
  let g : _root_.Point2 ≃ᵃⁱ[ℝ] _root_.Point2 :=
    directAffineIsometryEquivOfSendPair a c (xAxisPoint (-r)) (xAxisPoint r) hac htarget
  have hga : g a = xAxisPoint (-r) := by
    dsimp [g]
    exact directAffineIsometryEquivOfSendPair_apply_a _ _ _ _ _ _
  have hgc : g c = xAxisPoint r := by
    dsimp [g]
    exact directAffineIsometryEquivOfSendPair_apply_b _ _ _ _ _ _
  have hleft :
      ((g x) 0 + r) ^ 2 + ((g x) 1) ^ 2 =
        ((g y) 0 + r) ^ 2 + ((g y) 1) ^ 2 := by
    have hsq : dist (g x) (xAxisPoint (-r)) ^ 2 =
        dist (g y) (xAxisPoint (-r)) ^ 2 := by
      calc
        dist (g x) (xAxisPoint (-r)) ^ 2 = dist (g x) (g a) ^ 2 := by rw [hga]
        _ = dist x a ^ 2 := congrArg (fun z : ℝ ↦ z ^ 2) (g.dist_map x a)
        _ = dist y a ^ 2 := ha
        _ = dist (g y) (g a) ^ 2 :=
          (congrArg (fun z : ℝ ↦ z ^ 2) (g.dist_map y a)).symm
        _ = dist (g y) (xAxisPoint (-r)) ^ 2 := by rw [hga]
    rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq] at hsq
    simpa [xAxisPoint, Fin.sum_univ_two, Real.dist_eq] using hsq
  have hright :
      ((g x) 0 - r) ^ 2 + ((g x) 1) ^ 2 =
        ((g y) 0 - r) ^ 2 + ((g y) 1) ^ 2 := by
    have hsq : dist (g x) (xAxisPoint r) ^ 2 = dist (g y) (xAxisPoint r) ^ 2 := by
      calc
        dist (g x) (xAxisPoint r) ^ 2 = dist (g x) (g c) ^ 2 := by rw [hgc]
        _ = dist x c ^ 2 := congrArg (fun z : ℝ ↦ z ^ 2) (g.dist_map x c)
        _ = dist y c ^ 2 := hc
        _ = dist (g y) (g c) ^ 2 :=
          (congrArg (fun z : ℝ ↦ z ^ 2) (g.dist_map y c)).symm
        _ = dist (g y) (xAxisPoint r) ^ 2 := by rw [hgc]
    rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq] at hsq
    simpa [xAxisPoint, Fin.sum_univ_two, Real.dist_eq] using hsq
  have hfiber := twoAnchor_sqDistance_eq_same_or_reflection hr hleft hright
  refine ⟨g, r, hr, hga, hgc, ?_⟩
  rcases hfiber with hsame | hreflect
  · left
    apply g.injective
    ext i
    fin_cases i
    · exact hsame.1
    · exact hsame.2
  · exact Or.inr hreflect

end Esgk

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open scoped BigOperators

namespace Esgk


private lemma inline_Esgk_SharpResultantFiniteSetCount__remainingEval_injective :
    Function.Injective (MvPolynomial.eval bundle_Esgk_SharpResultantFiniteSetCount_remainingEval) := by
  rw [← MvPolynomial.aeval_eq_eval]
  exact (MvPolynomial.aeval_injective_iff_of_isEmpty.mpr (RingHom.injective _))

private lemma inline_Esgk_SharpResultantFiniteSetCount__headResultant_univariate_ne_zero
    (r : MvPolynomial (Fin 1) ℝ) (hr : r ≠ 0) :
    Polynomial.map (MvPolynomial.eval bundle_Esgk_SharpResultantFiniteSetCount_remainingEval) (headCurry r) ≠ 0 := by
  apply (Polynomial.map_ne_zero_iff inline_Esgk_SharpResultantFiniteSetCount__remainingEval_injective).mpr
  intro h
  apply hr
  exact (MvPolynomial.finSuccEquiv ℝ 0).injective h

private lemma inline_Esgk_SharpResultantFiniteSetCount__headResultant_univariate_natDegree_le
    (r : MvPolynomial (Fin 1) ℝ) :
    (Polynomial.map (MvPolynomial.eval bundle_Esgk_SharpResultantFiniteSetCount_remainingEval) (headCurry r)).natDegree ≤
      r.totalDegree := by
  calc
    (Polynomial.map (MvPolynomial.eval bundle_Esgk_SharpResultantFiniteSetCount_remainingEval) (headCurry r)).natDegree ≤
        (headCurry r).natDegree := Polynomial.natDegree_map_le
    _ = MvPolynomial.degreeOf 0 r := by
      simpa [headCurry] using (MvPolynomial.natDegree_finSuccEquiv (R := ℝ) (n := 0) r)
    _ ≤ r.totalDegree := MvPolynomial.degreeOf_le_totalDegree r 0

private lemma inline_Esgk_SharpResultantFiniteSetCount__headResultant_univariate_eval_eq_zero
    (r : MvPolynomial (Fin 1) ℝ) (z : Fin 2 → ℝ)
    (hz : MvPolynomial.eval (fun i : Fin 1 ↦ z i.succ) r = 0) :
    Polynomial.eval (z 1)
      (Polynomial.map (MvPolynomial.eval bundle_Esgk_SharpResultantFiniteSetCount_remainingEval) (headCurry r)) = 0 := by
  have hcoords :
      (fun i : Fin 1 ↦ z i.succ) = Fin.cons (z 1) bundle_Esgk_SharpResultantFiniteSetCount_remainingEval := by
    funext i
    fin_cases i
    rfl
  rw [hcoords] at hz
  simpa using
    (MvPolynomial.eval_eq_eval_mv_eval' (R := ℝ) bundle_Esgk_SharpResultantFiniteSetCount_remainingEval (z 1) r).symm ▸ hz


theorem common_zero_finset_card_le_totalDegree_mul
    (p q : MvPolynomial (Fin 2) ℝ) (S : Finset (Fin 2 → ℝ))
    (hpDegree : 0 < (headCurry p).natDegree)
    (hresultant : headResultant p q ≠ 0)
    (hprojection : Set.InjOn (fun z : Fin 2 → ℝ ↦ z 1) (S : Set (Fin 2 → ℝ)))
    (hzero : ∀ z ∈ S, MvPolynomial.eval z p = 0 ∧ MvPolynomial.eval z q = 0) :
    S.card ≤ p.totalDegree * q.totalDegree := by
  let r := headResultant p q
  let u : Polynomial ℝ := Polynomial.map (MvPolynomial.eval bundle_Esgk_SharpResultantFiniteSetCount_remainingEval) (headCurry r)
  let T : Finset ℝ := S.image (fun z : Fin 2 → ℝ ↦ z 1)
  have hcard : S.card = T.card := by
    exact (Finset.card_image_iff.mpr hprojection).symm
  have hr : r ≠ 0 := by
    simpa [r] using hresultant
  have hu : u ≠ 0 := by
    simpa [u] using inline_Esgk_SharpResultantFiniteSetCount__headResultant_univariate_ne_zero r hr
  have hTsubset : (T : Set ℝ) ⊆ u.rootSet ℝ := by
    intro y hy
    change y ∈ T at hy
    obtain ⟨z, hzS, rfl⟩ := Finset.mem_image.mp hy
    rw [Polynomial.mem_rootSet_of_ne hu]
    exact inline_Esgk_SharpResultantFiniteSetCount__headResultant_univariate_eval_eq_zero r z
      (eval_headResultant_eq_zero_of_common_zero p q z hpDegree
        (hzero z hzS).1 (hzero z hzS).2)
  have hTcard : T.card ≤ u.natDegree := by
    rw [← Set.ncard_coe_finset T]
    exact (Set.ncard_le_ncard hTsubset).trans (Polynomial.ncard_rootSet_le u ℝ)
  have huDegree : u.natDegree ≤ r.totalDegree := by
    simpa [u] using inline_Esgk_SharpResultantFiniteSetCount__headResultant_univariate_natDegree_le r
  rw [hcard]
  exact hTcard.trans huDegree |>.trans
    (headResultant_totalDegree_le_totalDegree_mul p q)

end Esgk
end

end


section
set_option autoImplicit true

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


set_option linter.style.longLine false

namespace PachDeZeeuw.Algebraic

open scoped Topology


scoped notation "E" => chartEquiv

 
@[simp] theorem chartEquiv_apply (x : PachDeZeeuw.Algebraic.Point2) : chartEquiv x = (x 0, x 1) := rfl

 
@[simp] theorem chartEquiv_fst (x : PachDeZeeuw.Algebraic.Point2) : (chartEquiv x).1 = x 0 := rfl

 
@[simp] theorem chartEquiv_snd (x : PachDeZeeuw.Algebraic.Point2) : (chartEquiv x).2 = x 1 := rfl

 
@[simp] theorem chartEquiv_symm_apply_zero (z : ℝ × ℝ) :
    (chartEquiv.symm z) 0 = z.1 := rfl

 
@[simp] theorem chartEquiv_symm_apply_one (z : ℝ × ℝ) :
    (chartEquiv.symm z) 1 = z.2 := rfl


theorem eval_eq_evalPlane_chart (p : PlanePoly) (x : PachDeZeeuw.Algebraic.Point2) :
    MvPolynomial.eval (fun i => x i) p = evalPlane p (chartEquiv x) := by
  unfold evalPlane
  refine congrArg (fun f => MvPolynomial.eval f p) ?_
  funext i
  fin_cases i <;> simp


end PachDeZeeuw.Algebraic

end


section
set_option autoImplicit true

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace PachDeZeeuw.Algebraic

open MvPolynomial


@[simp] lemma shearPoint_apply (s : ℝ) (p : ℝ × ℝ) :
    shearPoint s p = (p.1 - s * p.2, p.2) := rfl


theorem evalPlane_shearPoly_shearPoint (s : ℝ) (h : PlanePoly) (p : ℝ × ℝ) :
    evalPlane (shearPoly s h) (shearPoint s p) = evalPlane h p := by
   
  set pt : Fin 2 → ℝ :=
    (fun i => if i = 0 then (shearPoint s p).1 else (shearPoint s p).2) with hpt
   
  have h1 : evalPlane (shearPoly s h) (shearPoint s p)
      = (MvPolynomial.aeval pt) (MvPolynomial.aeval (shearVars s) h) := by
    rw [shearPoly, evalPlane, MvPolynomial.aeval_eq_eval]
  rw [h1]
   
   
  rw [MvPolynomial.comp_aeval_apply]
   
  have hpt0 : pt 0 = p.1 - s * p.2 := rfl
  have hpt1 : pt 1 = p.2 := rfl
   
  have hvars : (fun i => (MvPolynomial.aeval pt) (shearVars s i))
      = (fun i : Fin 2 => if i = 0 then p.1 else p.2) := by
    funext i
    fin_cases i
    ·  
      show (MvPolynomial.aeval pt) (MvPolynomial.X 0 + MvPolynomial.C s * MvPolynomial.X 1)
          = p.1
      rw [map_add, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
        Algebra.algebraMap_self_apply, hpt0, hpt1]
      ring
    ·  
      show (MvPolynomial.aeval pt) (MvPolynomial.X 1) = p.2
      rw [MvPolynomial.aeval_X, hpt1]
  rw [hvars, evalPlane, MvPolynomial.aeval_eq_eval]


theorem totalDegree_aeval_le {R : Type*} [CommSemiring R] {σ τ : Type*}
    (f : σ → MvPolynomial τ R) (hf : ∀ i, (f i).totalDegree ≤ 1) (p : MvPolynomial σ R) :
    (MvPolynomial.aeval f p).totalDegree ≤ p.totalDegree := by
  have hsum : MvPolynomial.aeval f p
      = ∑ v ∈ p.support, MvPolynomial.aeval f (MvPolynomial.monomial v (MvPolynomial.coeff v p)) := by
    conv_lhs => rw [p.as_sum]
    rw [map_sum]
  rw [hsum]
  refine MvPolynomial.totalDegree_finsetSum_le ?_
  intro v hv
  rw [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add, Finsupp.prod]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ v.support, (f i ^ v i).totalDegree
      ≤ ∑ i ∈ v.support, v i * (f i).totalDegree :=
        Finset.sum_le_sum (fun i _ => MvPolynomial.totalDegree_pow _ _)
    _ ≤ ∑ i ∈ v.support, v i * 1 :=
        Finset.sum_le_sum (fun i _ => Nat.mul_le_mul (le_refl (v i)) (hf i))
    _ = v.sum (fun _ e => e) := by simp only [mul_one]; rfl
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hv


lemma shearVars_totalDegree_le (s : ℝ) (i : Fin 2) : (shearVars s i).totalDegree ≤ 1 := by
  unfold shearVars
  split
  · refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · exact le_of_eq (totalDegree_X 0)
    · exact (totalDegree_mul _ _).trans (le_of_eq (by rw [totalDegree_C, totalDegree_X]))
  · exact le_of_eq (totalDegree_X 1)


theorem shearPoly_totalDegree_le (s : ℝ) (h : PlanePoly) :
    (shearPoly s h).totalDegree ≤ h.totalDegree := by
  unfold shearPoly
  exact totalDegree_aeval_le (shearVars s) (shearVars_totalDegree_le s) h

end PachDeZeeuw.Algebraic

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

namespace IrreduciblePlanePolynomial


@[simp]
theorem distanceImageFunctionFieldAlgEquivOfNonsymmetric_apply
    (C : IrreduciblePlanePolynomial ℝ) {r : ℝ} (hr : r ≠ 0)
    (hns :
      xAxisReflectionPoint '' PlaneCurveZeroSet C.polynomial ≠
        PlaneCurveZeroSet C.polynomial)
    (z : C.DistanceImageFunctionField r) :
    C.distanceImageFunctionFieldAlgEquivOfNonsymmetric hr hns z =
      C.distanceImageFunctionFieldHom r z :=
  rfl


theorem distanceImageFunctionFieldAlgEquivOfNonsymmetric_apply_coordinates
    (C : IrreduciblePlanePolynomial ℝ) {r : ℝ} (hr : r ≠ 0)
    (hns :
      xAxisReflectionPoint '' PlaneCurveZeroSet C.polynomial ≠
        PlaneCurveZeroSet C.polynomial) :
    C.distanceImageFunctionFieldAlgEquivOfNonsymmetric hr hns
          (C.distanceImageCoordinate r 0) =
        (C.coordinate 0 + algebraMap ℝ C.FunctionField r) ^ 2 +
          C.coordinate 1 ^ 2 ∧
      C.distanceImageFunctionFieldAlgEquivOfNonsymmetric hr hns
          (C.distanceImageCoordinate r 1) =
        (C.coordinate 0 - algebraMap ℝ C.FunctionField r) ^ 2 +
          C.coordinate 1 ^ 2 := by
  simpa using C.distanceImageFunctionFieldHom_apply_coordinates r

end IrreduciblePlanePolynomial

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open MvPolynomial

 
theorem bidegreeBound_iff_degreeOf_le {R : Type*} [CommSemiring R] (m : ℕ)
    (Q : BidegreePolynomial R) :
    BidegreeBound m Q ↔ degreeOf 0 Q ≤ m ∧ degreeOf 1 Q ≤ m := by
  constructor
  · intro hQ
    constructor <;> rw [degreeOf_le_iff] <;> intro e he
    · exact (hQ e he).1
    · exact (hQ e he).2
  · rintro ⟨hzero, hone⟩ e he
    exact ⟨degreeOf_le_iff.mp hzero e he, degreeOf_le_iff.mp hone e he⟩

 
theorem isotropicTranslation_monomial (ξ : ℂ) (e : Fin 2 →₀ ℕ) (c : ℂ) :
    isotropicTranslation ξ (monomial e c) =
      C c * (X 0 - C ξ) ^ e 0 * (X 1 - C (star ξ)) ^ e 1 := by
  rw [isotropicTranslation, eval₂Hom_monomial, Finsupp.prod_fintype]
  · simp [Fin.prod_univ_two, mul_assoc]
  · intro i
    simp

 
theorem degreeOf_isotropicTranslation_monomial_le (ξ : ℂ) (e : Fin 2 →₀ ℕ) (c : ℂ)
    (i : Fin 2) : degreeOf i (isotropicTranslation ξ (monomial e c)) ≤ e i := by
  rw [isotropicTranslation_monomial]
  fin_cases i
  · have hzero : degreeOf 0 (X 0 - C ξ : BidegreePolynomial ℂ) ≤ 1 := by
      simpa using degreeOf_sub_le 0 (X 0 : BidegreePolynomial ℂ) (C ξ)
    have hone : degreeOf 0 (X 1 - C (star ξ) : BidegreePolynomial ℂ) ≤ 0 := by
      simpa [degreeOf_X, show (0 : Fin 2) ≠ 1 by decide] using
        degreeOf_sub_le 0 (X 1 : BidegreePolynomial ℂ) (C (star ξ))
    have hpowZero := degreeOf_pow_le 0 (X 0 - C ξ : BidegreePolynomial ℂ) (e 0)
    have hpowOne := degreeOf_pow_le 0 (X 1 - C (star ξ) : BidegreePolynomial ℂ) (e 1)
    have hmulLeft :=
      degreeOf_mul_le 0 (C c : BidegreePolynomial ℂ) ((X 0 - C ξ) ^ e 0)
    have hmul := degreeOf_mul_le 0
      ((C c : BidegreePolynomial ℂ) * (X 0 - C ξ) ^ e 0)
      ((X 1 - C (star ξ)) ^ e 1)
    have hpowZero' : degreeOf 0 ((X 0 - C ξ : BidegreePolynomial ℂ) ^ e 0) ≤ e 0 := by
      calc
        _ ≤ e 0 * degreeOf 0 (X 0 - C ξ : BidegreePolynomial ℂ) := hpowZero
        _ ≤ e 0 * 1 := Nat.mul_le_mul_left _ hzero
        _ = e 0 := Nat.mul_one _
    have hpowOne' :
        degreeOf 0 ((X 1 - C (star ξ) : BidegreePolynomial ℂ) ^ e 1) ≤ 0 := by
      calc
        _ ≤ e 1 * degreeOf 0 (X 1 - C (star ξ) : BidegreePolynomial ℂ) := hpowOne
        _ ≤ e 1 * 0 := Nat.mul_le_mul_left _ hone
        _ = 0 := Nat.mul_zero _
    have hmulLeft' :
        degreeOf 0 ((C c : BidegreePolynomial ℂ) * (X 0 - C ξ) ^ e 0) ≤ e 0 := by
      calc
        _ ≤ degreeOf 0 (C c : BidegreePolynomial ℂ) +
            degreeOf 0 ((X 0 - C ξ) ^ e 0) := hmulLeft
        _ ≤ 0 + e 0 := Nat.add_le_add (by simp) hpowZero'
        _ = e 0 := Nat.zero_add _
    calc
      degreeOf 0 (C c * (X 0 - C ξ) ^ e 0 * (X 1 - C (star ξ)) ^ e 1)
          ≤ degreeOf 0 (C c * (X 0 - C ξ) ^ e 0) +
              degreeOf 0 ((X 1 - C (star ξ)) ^ e 1) := hmul
      _ ≤ e 0 + 0 := Nat.add_le_add hmulLeft' hpowOne'
      _ = e 0 := Nat.add_zero _
  · have hzero : degreeOf 1 (X 0 - C ξ : BidegreePolynomial ℂ) ≤ 0 := by
      simpa [degreeOf_X, show (1 : Fin 2) ≠ 0 by decide] using
        degreeOf_sub_le 1 (X 0 : BidegreePolynomial ℂ) (C ξ)
    have hone : degreeOf 1 (X 1 - C (star ξ) : BidegreePolynomial ℂ) ≤ 1 := by
      simpa using
        degreeOf_sub_le 1 (X 1 : BidegreePolynomial ℂ) (C (star ξ))
    have hpowZero := degreeOf_pow_le 1 (X 0 - C ξ : BidegreePolynomial ℂ) (e 0)
    have hpowOne := degreeOf_pow_le 1 (X 1 - C (star ξ) : BidegreePolynomial ℂ) (e 1)
    have hmulLeft :=
      degreeOf_mul_le 1 (C c : BidegreePolynomial ℂ) ((X 0 - C ξ) ^ e 0)
    have hmul := degreeOf_mul_le 1
      ((C c : BidegreePolynomial ℂ) * (X 0 - C ξ) ^ e 0)
      ((X 1 - C (star ξ)) ^ e 1)
    have hpowZero' : degreeOf 1 ((X 0 - C ξ : BidegreePolynomial ℂ) ^ e 0) ≤ 0 := by
      calc
        _ ≤ e 0 * degreeOf 1 (X 0 - C ξ : BidegreePolynomial ℂ) := hpowZero
        _ ≤ e 0 * 0 := Nat.mul_le_mul_left _ hzero
        _ = 0 := Nat.mul_zero _
    have hpowOne' :
        degreeOf 1 ((X 1 - C (star ξ) : BidegreePolynomial ℂ) ^ e 1) ≤ e 1 := by
      calc
        _ ≤ e 1 * degreeOf 1 (X 1 - C (star ξ) : BidegreePolynomial ℂ) := hpowOne
        _ ≤ e 1 * 1 := Nat.mul_le_mul_left _ hone
        _ = e 1 := Nat.mul_one _
    have hmulLeft' :
        degreeOf 1 ((C c : BidegreePolynomial ℂ) * (X 0 - C ξ) ^ e 0) ≤ 0 := by
      calc
        _ ≤ degreeOf 1 (C c : BidegreePolynomial ℂ) +
            degreeOf 1 ((X 0 - C ξ) ^ e 0) := hmulLeft
        _ ≤ 0 + 0 := Nat.add_le_add (by simp) hpowZero'
        _ = 0 := Nat.zero_add _
    calc
      degreeOf 1 (C c * (X 0 - C ξ) ^ e 0 * (X 1 - C (star ξ)) ^ e 1)
          ≤ degreeOf 1 (C c * (X 0 - C ξ) ^ e 0) +
              degreeOf 1 ((X 1 - C (star ξ)) ^ e 1) := hmul
      _ ≤ 0 + e 1 := Nat.add_le_add hmulLeft' hpowOne'
      _ = e 1 := Nat.zero_add _

 
theorem degreeOf_isotropicTranslation_le (ξ : ℂ) (Q : BidegreePolynomial ℂ) (i : Fin 2) :
    degreeOf i (isotropicTranslation ξ Q) ≤ degreeOf i Q := by
  conv_lhs => rw [Q.as_sum]
  rw [map_sum]
  refine (degreeOf_sum_le i Q.support fun e ↦
    isotropicTranslation ξ (monomial e (coeff e Q))).trans ?_
  rw [degreeOf_eq_sup]
  exact Finset.sup_le fun e he ↦
    (degreeOf_isotropicTranslation_monomial_le ξ e (coeff e Q) i).trans
      (Finset.le_sup (f := fun d : Fin 2 →₀ ℕ ↦ d i) he)


theorem bidegreeBound_isotropicTranslation (ξ : ℂ) (m : ℕ) {Q : BidegreePolynomial ℂ}
    (hQ : BidegreeBound m Q) : BidegreeBound m (isotropicTranslation ξ Q) := by
  rw [bidegreeBound_iff_degreeOf_le] at hQ ⊢
  exact ⟨(degreeOf_isotropicTranslation_le ξ Q 0).trans hQ.1,
    (degreeOf_isotropicTranslation_le ξ Q 1).trans hQ.2⟩

 
theorem totalDegree_le_two_mul_of_bidegreeBound {R : Type*} [CommSemiring R] (m : ℕ)
    {Q : BidegreePolynomial R} (hQ : BidegreeBound m Q) : totalDegree Q ≤ 2 * m := by
  rw [totalDegree]
  refine Finset.sup_le fun e he ↦ ?_
  have hzero := (hQ e he).1
  have hone := (hQ e he).2
  rw [Finsupp.sum_fintype _ _ (fun _ ↦ rfl)]
  simp only [Fin.sum_univ_two]
  omega


end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open PachDeZeeuw.Algebraic


lemma same_or_reflection_of_normalized_pair
    {r x₁ y₁ x₂ y₂ : ℝ} (hr : r ≠ 0)
    (hleft : (x₁ + r) ^ 2 + y₁ ^ 2 = (x₂ + r) ^ 2 + y₂ ^ 2)
    (hright : (x₁ - r) ^ 2 + y₁ ^ 2 = (x₂ - r) ^ 2 + y₂ ^ 2) :
    (x₁ = x₂ ∧ y₁ = y₂) ∨ (x₁ = x₂ ∧ y₁ = -y₂) := by
  have hprod : r * (x₁ - x₂) = 0 := by
    nlinarith [hleft, hright]
  have hx : x₁ = x₂ := by
    have hdiff : x₁ - x₂ = 0 := (mul_eq_zero.mp hprod).resolve_left hr
    linarith
  have hysq : y₁ ^ 2 = y₂ ^ 2 := by
    have hleft' := hleft
    rw [hx] at hleft'
    nlinarith [hleft']
  exact (sq_eq_sq_iff_eq_or_eq_neg.mp hysq).imp (fun h ↦ ⟨hx, h⟩)
    (fun h ↦ ⟨hx, h⟩)

 
lemma infinite_image_of_infinite_finite_fibers
    {α β : Type*} {U : Set α} {f : α → β} (hU : U.Infinite)
    (hfibers : ∀ y, (U ∩ f ⁻¹' {y}).Finite) :
    (f '' U).Infinite := by
  intro himage
  apply hU
  apply Set.Finite.of_finite_fibers f himage
  intro y hy
  exact hfibers y


lemma normalized_projection_fst_fiber_finite
    {U : Set (PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2)} {r₁ r₂ : ℝ} (hr₂ : r₂ ≠ 0)
    (hleft : ∀ p ∈ U, normalizedLeftValue r₁ p.1 = normalizedLeftValue r₂ p.2)
    (hright : ∀ p ∈ U, normalizedRightValue r₁ p.1 = normalizedRightValue r₂ p.2)
    (x : PachDeZeeuw.Algebraic.Point2) : (U ∩ Prod.fst ⁻¹' {x}).Finite := by
  by_cases hne : (U ∩ Prod.fst ⁻¹' {x}).Nonempty
  · obtain ⟨p, hpU, hpx⟩ := hne
    have hpx' : p.1 = x := hpx
    let y₀ : PachDeZeeuw.Algebraic.Point2 := p.2
    have hsub : U ∩ Prod.fst ⁻¹' {x} ⊆
      ({(x, y₀), (x, xAxisReflectionPoint y₀)} : Set (PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2)) := by
      intro q hq
      have hqx : q.1 = x := hq.2
      have hL : normalizedLeftValue r₂ q.2 = normalizedLeftValue r₂ p.2 := by
        calc
          normalizedLeftValue r₂ q.2 = normalizedLeftValue r₁ q.1 :=
            (hleft q hq.1).symm
          _ = normalizedLeftValue r₁ p.1 := by rw [hqx, hpx']
          _ = normalizedLeftValue r₂ p.2 := hleft p hpU
      have hR : normalizedRightValue r₂ q.2 = normalizedRightValue r₂ p.2 := by
        calc
          normalizedRightValue r₂ q.2 = normalizedRightValue r₁ q.1 :=
            (hright q hq.1).symm
          _ = normalizedRightValue r₁ p.1 := by rw [hqx, hpx']
          _ = normalizedRightValue r₂ p.2 := hright p hpU
      have hpair := same_or_reflection_of_normalized_pair hr₂
        (x₁ := q.2 0) (y₁ := q.2 1) (x₂ := p.2 0) (y₂ := p.2 1) (by
          simpa [normalizedLeftValue] using hL) (by
          simpa [normalizedRightValue] using hR)
      rcases hpair with hsame | hreflect
      · left
        apply Prod.ext hqx
        ext i
        fin_cases i
        · exact hsame.1
        · exact hsame.2
      · right
        apply Prod.ext hqx
        ext i
        fin_cases i
        · exact hreflect.1
        · simpa [xAxisReflectionPoint] using hreflect.2
    exact ((Set.finite_singleton _).insert _).subset hsub
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact Set.finite_empty


lemma normalized_projection_fst_infinite
    {U : Set (PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2)} {r₁ r₂ : ℝ} (hU : U.Infinite) (hr₂ : r₂ ≠ 0)
    (hleft : ∀ p ∈ U, normalizedLeftValue r₁ p.1 = normalizedLeftValue r₂ p.2)
    (hright : ∀ p ∈ U, normalizedRightValue r₁ p.1 = normalizedRightValue r₂ p.2) :
    (Prod.fst '' U).Infinite :=
  infinite_image_of_infinite_finite_fibers hU
    (normalized_projection_fst_fiber_finite hr₂ hleft hright)


lemma normalized_projection_snd_fiber_finite
    {U : Set (PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2)} {r₁ r₂ : ℝ} (hr₁ : r₁ ≠ 0)
    (hleft : ∀ p ∈ U, normalizedLeftValue r₁ p.1 = normalizedLeftValue r₂ p.2)
    (hright : ∀ p ∈ U, normalizedRightValue r₁ p.1 = normalizedRightValue r₂ p.2)
    (y : PachDeZeeuw.Algebraic.Point2) : (U ∩ Prod.snd ⁻¹' {y}).Finite := by
  by_cases hne : (U ∩ Prod.snd ⁻¹' {y}).Nonempty
  · obtain ⟨p, hpU, hpy⟩ := hne
    have hpy' : p.2 = y := hpy
    let x₀ : PachDeZeeuw.Algebraic.Point2 := p.1
    have hsub : U ∩ Prod.snd ⁻¹' {y} ⊆
      ({(x₀, y), (xAxisReflectionPoint x₀, y)} : Set (PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2)) := by
      intro q hq
      have hqy : q.2 = y := hq.2
      have hL : normalizedLeftValue r₁ q.1 = normalizedLeftValue r₁ p.1 := by
        calc
          normalizedLeftValue r₁ q.1 = normalizedLeftValue r₂ q.2 := hleft q hq.1
          _ = normalizedLeftValue r₂ p.2 := by rw [hqy, hpy']
          _ = normalizedLeftValue r₁ p.1 := (hleft p hpU).symm
      have hR : normalizedRightValue r₁ q.1 = normalizedRightValue r₁ p.1 := by
        calc
          normalizedRightValue r₁ q.1 = normalizedRightValue r₂ q.2 := hright q hq.1
          _ = normalizedRightValue r₂ p.2 := by rw [hqy, hpy']
          _ = normalizedRightValue r₁ p.1 := (hright p hpU).symm
      have hpair := same_or_reflection_of_normalized_pair hr₁
        (x₁ := q.1 0) (y₁ := q.1 1) (x₂ := p.1 0) (y₂ := p.1 1) (by
          simpa [normalizedLeftValue] using hL) (by
          simpa [normalizedRightValue] using hR)
      rcases hpair with hsame | hreflect
      · left
        apply Prod.ext
        · ext i
          fin_cases i
          · exact hsame.1
          · exact hsame.2
        · exact hqy
      · right
        apply Prod.ext
        · ext i
          fin_cases i
          · exact hreflect.1
          · simpa [xAxisReflectionPoint] using hreflect.2
        · exact hqy
    exact ((Set.finite_singleton _).insert _).subset hsub
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact Set.finite_empty


lemma normalized_projection_snd_infinite
    {U : Set (PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2)} {r₁ r₂ : ℝ} (hU : U.Infinite) (hr₁ : r₁ ≠ 0)
    (hleft : ∀ p ∈ U, normalizedLeftValue r₁ p.1 = normalizedLeftValue r₂ p.2)
    (hright : ∀ p ∈ U, normalizedRightValue r₁ p.1 = normalizedRightValue r₂ p.2) :
    (Prod.snd '' U).Infinite :=
  infinite_image_of_infinite_finite_fibers hU
    (normalized_projection_snd_fiber_finite hr₁ hleft hright)

end Esgk

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic


theorem planeAffinePolynomialEquiv_symm_apply_squaredDistance
    (g : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) (a : PachDeZeeuw.Algebraic.Point2) :
    planeAffinePolynomialEquiv g.symm (planeSquaredDistancePolynomial a) =
      planeSquaredDistancePolynomial (g a) := by
  apply MvPolynomial.funext
  intro z
  let x : PachDeZeeuw.Algebraic.Point2 := WithLp.toLp 2 z
  calc
    MvPolynomial.eval z
        (planeAffinePolynomialEquiv g.symm
          (planeSquaredDistancePolynomial a)) =
        dist (g.symm x) a ^ 2 := by
      rw [eval_planeAffinePolynomialEquiv]
      simp [x]
    _ = dist x (g a) ^ 2 := by
      have hdist := g.dist_map (g.symm x) a
      apply congrArg (fun t : ℝ ↦ t ^ 2)
      simpa using hdist.symm
    _ = MvPolynomial.eval z
        (planeSquaredDistancePolynomial (g a)) := by
      simpa [x] using (eval_planeSquaredDistancePolynomial (g a) x).symm


@[simp]
theorem planeSquaredDistancePolynomial_xAxisPoint (r : ℝ) :
    planeSquaredDistancePolynomial (xAxisPoint r) =
      (MvPolynomial.X 0 - MvPolynomial.C r) ^ 2 +
        MvPolynomial.X 1 ^ 2 := by
  simp [planeSquaredDistancePolynomial, xAxisPoint]

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open MvPolynomial


theorem totalDegree_eval₂Hom_le_of_isHomogeneous_one
    {R S σ τ : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* MvPolynomial τ S) (g : σ → MvPolynomial τ S)
    (hf : ∀ r, (f r).IsHomogeneous 0)
    (hg : ∀ i, (g i).IsHomogeneous 1)
    (P : MvPolynomial σ R) :
    ((MvPolynomial.eval₂Hom f g) P).totalDegree ≤ P.totalDegree := by
  conv_lhs => rw [← P.sum_homogeneousComponent]
  rw [map_sum (MvPolynomial.eval₂Hom f g)]
  refine MvPolynomial.totalDegree_finsetSum_le (d := P.totalDegree) ?_
  intro d hd
  have hhom :=
    (MvPolynomial.homogeneousComponent_isHomogeneous d P).eval₂ f g hf hg
  have hterm :
      ((MvPolynomial.eval₂Hom f g)
        (MvPolynomial.homogeneousComponent d P)).totalDegree ≤ d := by
    simpa only [MvPolynomial.coe_eval₂Hom, Nat.one_mul] using hhom.totalDegree_le
  have hle : d ≤ P.totalDegree := by
    simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hd
  exact hterm.trans hle

private theorem inline_Esgk_PlaneIsotropicDegree__planeToIsotropicCoordinates_image_isHomogeneous
    (i : Fin 2) :
    (![MvPolynomial.C (1 / 2 : ℂ) * (MvPolynomial.X 0 + MvPolynomial.X 1),
        MvPolynomial.C (1 / (2 * Complex.I)) *
          (MvPolynomial.X 0 - MvPolynomial.X 1)] i : ComplexPlanePoly).IsHomogeneous 1 := by
  fin_cases i
  · exact ((MvPolynomial.isHomogeneous_X ℂ 0).add
      (MvPolynomial.isHomogeneous_X ℂ 1)).C_mul _
  · exact ((MvPolynomial.isHomogeneous_X ℂ 0).sub
      (MvPolynomial.isHomogeneous_X ℂ 1)).C_mul _

private theorem inline_Esgk_PlaneIsotropicDegree__isotropicToPlaneCoordinates_image_isHomogeneous
    (i : Fin 2) :
    (![MvPolynomial.X 0 + MvPolynomial.C Complex.I * MvPolynomial.X 1,
        MvPolynomial.X 0 - MvPolynomial.C Complex.I * MvPolynomial.X 1] i :
      ComplexPlanePoly).IsHomogeneous 1 := by
  fin_cases i
  · exact (MvPolynomial.isHomogeneous_X ℂ 0).add
      ((MvPolynomial.isHomogeneous_X ℂ 1).C_mul _)
  · exact (MvPolynomial.isHomogeneous_X ℂ 0).sub
      ((MvPolynomial.isHomogeneous_X ℂ 1).C_mul _)

 
theorem planeToIsotropicCoordinates_totalDegree_le (P : ComplexPlanePoly) :
    (planeToIsotropicCoordinates P).totalDegree ≤ P.totalDegree := by
  exact totalDegree_eval₂Hom_le_of_isHomogeneous_one
    (MvPolynomial.C : ℂ →+* ComplexPlanePoly)
    ![MvPolynomial.C (1 / 2 : ℂ) * (MvPolynomial.X 0 + MvPolynomial.X 1),
      MvPolynomial.C (1 / (2 * Complex.I)) *
        (MvPolynomial.X 0 - MvPolynomial.X 1)]
    (fun c ↦ MvPolynomial.isHomogeneous_C (σ := Fin 2) c)
    inline_Esgk_PlaneIsotropicDegree__planeToIsotropicCoordinates_image_isHomogeneous P

 
theorem isotropicToPlaneCoordinates_totalDegree_le (P : ComplexPlanePoly) :
    (isotropicToPlaneCoordinates P).totalDegree ≤ P.totalDegree := by
  exact totalDegree_eval₂Hom_le_of_isHomogeneous_one
    (MvPolynomial.C : ℂ →+* ComplexPlanePoly)
    ![MvPolynomial.X 0 + MvPolynomial.C Complex.I * MvPolynomial.X 1,
      MvPolynomial.X 0 - MvPolynomial.C Complex.I * MvPolynomial.X 1]
    (fun c ↦ MvPolynomial.isHomogeneous_C (σ := Fin 2) c)
    inline_Esgk_PlaneIsotropicDegree__isotropicToPlaneCoordinates_image_isHomogeneous P

 
theorem planeToIsotropicCoordinates_totalDegree (P : ComplexPlanePoly) :
    (planeToIsotropicCoordinates P).totalDegree = P.totalDegree := by
  apply Nat.le_antisymm (planeToIsotropicCoordinates_totalDegree_le P)
  have hcomp :
      isotropicToPlaneCoordinates (planeToIsotropicCoordinates P) = P :=
    RingHom.congr_fun
      isotropicToPlaneCoordinates_comp_planeToIsotropicCoordinates P
  calc
    P.totalDegree =
        (isotropicToPlaneCoordinates (planeToIsotropicCoordinates P)).totalDegree := by
      rw [hcomp]
    _ ≤ (planeToIsotropicCoordinates P).totalDegree :=
      isotropicToPlaneCoordinates_totalDegree_le _


end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace PachDeZeeuw.Algebraic

open MvPolynomial


theorem eval_shearPoly_shearPoint_chart (s : ℝ) (h : PlanePoly) (z : PachDeZeeuw.Algebraic.Point2) :
    MvPolynomial.eval
        (fun i ↦ (chartEquiv.symm (shearPoint s (chartEquiv z))) i)
        (shearPoly s h) =
      MvPolynomial.eval (fun i ↦ z i) h := by
  rw [eval_eq_evalPlane_chart, Homeomorph.apply_symm_apply,
    evalPlane_shearPoly_shearPoint, ← eval_eq_evalPlane_chart]


theorem eval_rename_swap_swapPoint (h : PlanePoly) (z : PachDeZeeuw.Algebraic.Point2) :
    MvPolynomial.eval (fun i ↦ swapPoint z i)
        (MvPolynomial.rename (Equiv.swap 0 1) h) =
      MvPolynomial.eval (fun i ↦ z i) h := by
  rw [MvPolynomial.eval_rename]
  have hcoords :
      ((fun i ↦ swapPoint z i) ∘ (Equiv.swap 0 1)) = fun i ↦ z i := by
    funext i
    fin_cases i <;> simp [Function.comp, swapPoint, mkPoint2]
  rw [hcoords]


end PachDeZeeuw.Algebraic
end

end


section
set_option autoImplicit true

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace PachDeZeeuw.Algebraic

open MvPolynomial


@[simp] lemma shearAlgEquiv_apply (s : ℝ) (h : PlanePoly) :
    shearAlgEquiv s h = shearPoly s h := by
  rw [shearAlgEquiv, AlgEquiv.ofAlgHom_apply]
  rfl


theorem irreducible_shearPoly_iff (s : ℝ) (h : PlanePoly) :
    Irreducible (shearPoly s h) ↔ Irreducible h := by
  rw [← shearAlgEquiv_apply s h]
  exact MulEquiv.irreducible_iff (shearAlgEquiv s)

end PachDeZeeuw.Algebraic

end


section
set_option autoImplicit true

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace PachDeZeeuw.Algebraic

open MvPolynomial


private theorem inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__msum_eq (m : Fin 2 →₀ ℕ) : (m.sum fun _ e => e) = m 0 + m 1 := by
  rw [Finsupp.sum, ← Finsupp.degree_apply, Finsupp.degree_eq_sum, Fin.sum_univ_two]

 
private theorem inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__sum_support_single (D : ℕ) :
    ∑ i ∈ (Finsupp.single (1 : Fin 2) D).support, (Finsupp.single (1 : Fin 2) D) i = D := by
  rw [← Finsupp.degree_apply, Finsupp.degree_single]


private theorem inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__coeff_single_one_pow (s : ℝ) (a : ℕ) :
    coeff (Finsupp.single (1 : Fin 2) a) ((X 0 + C s * X 1) ^ a) = s ^ a := by
  classical
  induction a with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_add, coeff_add]
    have hX0 : coeff (Finsupp.single (1 : Fin 2) (n + 1)) ((X 0 + C s * X 1) ^ n * X 0) = 0 := by
      rw [coeff_mul_X', if_neg]; simp [Finsupp.mem_support_iff]
    have hX1 : coeff (Finsupp.single (1 : Fin 2) (n + 1)) ((X 0 + C s * X 1) ^ n * (C s * X 1))
        = s ^ (n + 1) := by
      rw [show (X 0 + C s * X 1 : PlanePoly) ^ n * (C s * X 1)
            = C s * ((X 0 + C s * X 1) ^ n * X 1) by ring, coeff_C_mul,
          show (Finsupp.single (1 : Fin 2) (n + 1))
            = (Finsupp.single (1 : Fin 2) n) + (Finsupp.single (1 : Fin 2) 1) by
              rw [← Finsupp.single_add], coeff_mul_X, ih]
      ring
    rw [hX0, hX1, zero_add]


private theorem inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__shear_monomial (s : ℝ) (m : Fin 2 →₀ ℕ) (c : ℝ) :
    shearPoly s (monomial m c) = C c * (X 0 + C s * X 1) ^ (m 0) * (X 1) ^ (m 1) := by
  unfold shearPoly shearVars
  rw [aeval_monomial, MvPolynomial.algebraMap_eq,
    Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp only [Fin.prod_univ_two, Fin.isValue, if_true, if_neg (by decide : (1 : Fin 2) ≠ 0)]
  ring


private theorem inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__coeff_yD_shear_monomial (s : ℝ) (m : Fin 2 →₀ ℕ) (c : ℝ) :
    coeff (Finsupp.single (1 : Fin 2) (m 0 + m 1)) (shearPoly s (monomial m c))
      = c * s ^ (m 0) := by
  classical
  rw [inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__shear_monomial, X_pow_eq_monomial, mul_assoc, coeff_C_mul,
    show (Finsupp.single (1 : Fin 2) (m 0 + m 1))
        = (Finsupp.single (1 : Fin 2) (m 0)) + (Finsupp.single (1 : Fin 2) (m 1)) by
        rw [← Finsupp.single_add],
    coeff_mul_monomial, inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__coeff_single_one_pow, mul_one]


private theorem inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__coeff_yD_shear_monomial_lt (s : ℝ) (D : ℕ) (m : Fin 2 →₀ ℕ) (c : ℝ)
    (hlt : m 0 + m 1 < D) :
    coeff (Finsupp.single (1 : Fin 2) D) (shearPoly s (monomial m c)) = 0 := by
  apply coeff_eq_zero_of_totalDegree_lt
  rw [inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__sum_support_single]
  refine lt_of_le_of_lt (shearPoly_totalDegree_le s (monomial m c)) ?_
  refine lt_of_le_of_lt (totalDegree_monomial_le m c) ?_
  rw [Function.id_def, inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__msum_eq]
  exact hlt


theorem coeff_yD_shear_eq_eval (h : PlanePoly) (s : ℝ) :
    coeff (Finsupp.single (1 : Fin 2) h.totalDegree) (shearPoly s h)
      = (shearTopPoly h).eval s := by
  classical
  set D := h.totalDegree with hD
  have hexp : shearPoly s h
      = ∑ m ∈ h.support, shearPoly s (monomial m (coeff m h)) := by
    conv_lhs => rw [h.as_sum]
    rw [shearPoly, map_sum]
    rfl
  rw [hexp, coeff_sum, shearTopPoly, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro m hm
  have hle : m 0 + m 1 ≤ D := by
    rw [hD, ← inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__msum_eq m]; exact le_totalDegree hm
  rcases eq_or_lt_of_le hle with heq | hlt
  · rw [if_pos (heq.trans hD)]
    have hidx : (Finsupp.single (1 : Fin 2) D) = Finsupp.single (1 : Fin 2) (m 0 + m 1) := by
      rw [heq]
    rw [hidx, inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__coeff_yD_shear_monomial]
    simp [Polynomial.eval_mul, Polynomial.eval_pow]
  · rw [if_neg (by omega), inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__coeff_yD_shear_monomial_lt s D m (coeff m h) hlt]
    simp


theorem shearTopPoly_ne_zero (h : PlanePoly) (hh : h ≠ 0) : shearTopPoly h ≠ 0 := by
  classical
  set D := h.totalDegree with hD
  have hne : h.support.Nonempty := by
    rwa [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
  obtain ⟨m0, hm0, hsup⟩ :=
    Finset.exists_mem_eq_sup h.support hne (fun s => s.sum fun _ e => e)
  have hm0deg : m0 0 + m0 1 = D := by rw [← inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__msum_eq m0, ← hsup]; rfl
  have hcoeff0 : coeff m0 h ≠ 0 := MvPolynomial.mem_support_iff.mp hm0
  intro hzero
  apply hcoeff0
  have hkey : (shearTopPoly h).coeff (m0 0) = coeff m0 h := by
    rw [shearTopPoly, Polynomial.finsetSum_coeff, Finset.sum_eq_single m0]
    · rw [if_pos hm0deg, Polynomial.coeff_C_mul_X_pow, if_pos rfl]
    · intro m _ hmm0
      by_cases hmd : m 0 + m 1 = D
      · rw [if_pos hmd, Polynomial.coeff_C_mul_X_pow, if_neg]
        intro hm00
        apply hmm0
        have hm00' : m 0 = m0 0 := hm00.symm
        have hm1 : m 1 = m0 1 := by omega
        apply Finsupp.ext
        intro i
        match i with
        | 0 => exact hm00'
        | 1 => exact hm1
      · rw [if_neg hmd, Polynomial.coeff_zero]
    · intro hm
      exact absurd hm0 (by rw [MvPolynomial.notMem_support_iff] at hm ⊢; exact hm)
  rw [hzero, Polynomial.coeff_zero] at hkey
  exact hkey.symm


private theorem inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__coeff_X_mul_pderiv (i : Fin 2) (g : PlanePoly) (m : Fin 2 →₀ ℕ) :
    coeff m (X i * pderiv i g) = (m i) • coeff m g := by
  classical
  have hexp : X i * pderiv i g
      = ∑ v ∈ g.support, (v i) • monomial v (coeff v g) := by
    conv_lhs => rw [g.as_sum]
    rw [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [X_mul_pderiv_monomial]
  rw [hexp, coeff_sum]
  simp only [coeff_smul, coeff_monomial]
  rw [Finset.sum_eq_single m]
  · rw [if_pos rfl]
  · intro v _ hvm
    rw [if_neg (fun h => hvm h), smul_zero]
  · intro hm
    rw [notMem_support_iff] at hm
    rw [if_pos rfl, hm, smul_zero]


private theorem inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__coeff_yD_eq_zero_of_pderiv_eq_zero (g : PlanePoly) (D : ℕ) (hD : 1 ≤ D)
    (h0 : pderiv (1 : Fin 2) g = 0) :
    coeff (Finsupp.single (1 : Fin 2) D) g = 0 := by
  have hco := inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__coeff_X_mul_pderiv (1 : Fin 2) g (Finsupp.single (1 : Fin 2) D)
  rw [h0, mul_zero, coeff_zero] at hco
  rw [Finsupp.single_eq_same, nsmul_eq_mul] at hco
  have hDpos : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact (mul_eq_zero.mp hco.symm).resolve_left hDpos


theorem partialY_shearPoly_finite_bad (h : PlanePoly) (hpos : 1 ≤ h.totalDegree) :
    {s : ℝ | MvPolynomial.pderiv (1 : Fin 2) (shearPoly s h) = 0}.Finite := by
  have hh : h ≠ 0 := by
    intro h0
    rw [h0, totalDegree_zero] at hpos
    exact absurd hpos (by norm_num)
  have hPne : shearTopPoly h ≠ 0 := shearTopPoly_ne_zero h hh
  apply Set.Finite.subset (Polynomial.finite_setOfPred_isRoot hPne)
  intro s hs
  simp only [Set.mem_ofPred_eq] at hs ⊢
   
  rw [Polynomial.IsRoot.def, ← coeff_yD_shear_eq_eval]
  exact inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__coeff_yD_eq_zero_of_pderiv_eq_zero (shearPoly s h) h.totalDegree hpos hs

end PachDeZeeuw.Algebraic

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

namespace IrreduciblePlanePolynomial


@[simp]
theorem squaredDistanceClassAt_xAxisPoint_neg
    (C : IrreduciblePlanePolynomial ℝ) (r : ℝ) :
    C.squaredDistanceClassAt (xAxisPoint (-r)) =
      C.leftSquaredDistanceClass r := by
  simp [squaredDistanceClassAt, leftSquaredDistanceClass, coordinateClass]
  rw [← MvPolynomial.algebraMap_eq]
  rw [Ideal.Quotient.mk_algebraMap]

@[simp]
theorem squaredDistanceClassAt_xAxisPoint
    (C : IrreduciblePlanePolynomial ℝ) (r : ℝ) :
    C.squaredDistanceClassAt (xAxisPoint r) =
      C.rightSquaredDistanceClass r := by
  simp [squaredDistanceClassAt, rightSquaredDistanceClass, coordinateClass]
  rw [← MvPolynomial.algebraMap_eq]
  rw [Ideal.Quotient.mk_algebraMap]

@[simp]
theorem squaredDistanceFunctionAt_xAxisPoint_neg
    (C : IrreduciblePlanePolynomial ℝ) (r : ℝ) :
    C.squaredDistanceFunctionAt (xAxisPoint (-r)) =
      algebraMap C.CoordinateRing C.FunctionField
        (C.leftSquaredDistanceClass r) := by
  rw [squaredDistanceFunctionAt, C.squaredDistanceClassAt_xAxisPoint_neg]

@[simp]
theorem squaredDistanceFunctionAt_xAxisPoint
    (C : IrreduciblePlanePolynomial ℝ) (r : ℝ) :
    C.squaredDistanceFunctionAt (xAxisPoint r) =
      algebraMap C.CoordinateRing C.FunctionField
        (C.rightSquaredDistanceClass r) := by
  rw [squaredDistanceFunctionAt, C.squaredDistanceClassAt_xAxisPoint]


@[simp]
theorem affineIsometryCoordinateRingAlgEquiv_apply_squaredDistanceClassAt
    (C : IrreduciblePlanePolynomial ℝ)
    (g : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) (a : PachDeZeeuw.Algebraic.Point2) :
    C.affineIsometryCoordinateRingAlgEquiv g
        (C.squaredDistanceClassAt a) =
      (C.affineIsometryTransport g).squaredDistanceClassAt (g a) := by
  change
    C.coordinateRingAlgEquivTransport (planeAffinePolynomialEquiv g.symm)
        (Ideal.Quotient.mk _ (planeSquaredDistancePolynomial a)) =
      Ideal.Quotient.mk _ (planeSquaredDistancePolynomial (g a))
  rw [C.coordinateRingAlgEquivTransport_apply_mk]
  rw [planeAffinePolynomialEquiv_symm_apply_squaredDistance]


@[simp]
theorem affineIsometryFunctionFieldAlgEquiv_apply_squaredDistanceFunctionAt
    (C : IrreduciblePlanePolynomial ℝ)
    (g : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) (a : PachDeZeeuw.Algebraic.Point2) :
    C.affineIsometryFunctionFieldAlgEquiv g
        (C.squaredDistanceFunctionAt a) =
      (C.affineIsometryTransport g).squaredDistanceFunctionAt (g a) := by
  change
    C.functionFieldAlgEquivTransport (planeAffinePolynomialEquiv g.symm)
        (algebraMap C.CoordinateRing C.FunctionField
          (C.squaredDistanceClassAt a)) =
      algebraMap (C.affineIsometryTransport g).CoordinateRing
        (C.affineIsometryTransport g).FunctionField
        ((C.affineIsometryTransport g).squaredDistanceClassAt (g a))
  rw [C.functionFieldAlgEquivTransport_apply_algebraMap]
  congr 1
  exact C.affineIsometryCoordinateRingAlgEquiv_apply_squaredDistanceClassAt g a


theorem affineIsometryFunctionFieldAlgEquiv_apply_squaredDistance_pair
    (C : IrreduciblePlanePolynomial ℝ)
    (g : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) (a c : PachDeZeeuw.Algebraic.Point2) (r : ℝ)
    (hga : g a = xAxisPoint (-r))
    (hgc : g c = xAxisPoint r) :
    C.affineIsometryFunctionFieldAlgEquiv g
          (C.squaredDistanceFunctionAt a) =
        algebraMap (C.affineIsometryTransport g).CoordinateRing
          (C.affineIsometryTransport g).FunctionField
          ((C.affineIsometryTransport g).leftSquaredDistanceClass r) ∧
      C.affineIsometryFunctionFieldAlgEquiv g
          (C.squaredDistanceFunctionAt c) =
        algebraMap (C.affineIsometryTransport g).CoordinateRing
          (C.affineIsometryTransport g).FunctionField
          ((C.affineIsometryTransport g).rightSquaredDistanceClass r) := by
  constructor
  · rw [C.affineIsometryFunctionFieldAlgEquiv_apply_squaredDistanceFunctionAt]
    rw [hga]
    exact (C.affineIsometryTransport g).squaredDistanceFunctionAt_xAxisPoint_neg r
  · rw [C.affineIsometryFunctionFieldAlgEquiv_apply_squaredDistanceFunctionAt]
    rw [hgc]
    exact (C.affineIsometryTransport g).squaredDistanceFunctionAt_xAxisPoint r


theorem exists_affineIsometryTransport_normalizedDistancePair
    (C : IrreduciblePlanePolynomial ℝ) {a c : PachDeZeeuw.Algebraic.Point2} (hac : a ≠ c) :
    ∃ (g : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) (r : ℝ),
      0 < r ∧
        g a = xAxisPoint (-r) ∧
        g c = xAxisPoint r ∧
        g '' PlaneCurveZeroSet C.polynomial =
          PlaneCurveZeroSet (C.affineIsometryTransport g).polynomial ∧
        (C.affineIsometryFunctionFieldAlgEquiv g
              (C.squaredDistanceFunctionAt a) =
            algebraMap (C.affineIsometryTransport g).CoordinateRing
              (C.affineIsometryTransport g).FunctionField
              ((C.affineIsometryTransport g).leftSquaredDistanceClass r) ∧
          C.affineIsometryFunctionFieldAlgEquiv g
              (C.squaredDistanceFunctionAt c) =
            algebraMap (C.affineIsometryTransport g).CoordinateRing
              (C.affineIsometryTransport g).FunctionField
              ((C.affineIsometryTransport g).rightSquaredDistanceClass r)) := by
  obtain ⟨g, r, hr, hga, hgc, _⟩ :=
    exists_normalizing_isometry_twoAnchor_fiber_dichotomy
      (a := a) (c := c) (x := a) (y := a) hac rfl rfl
  refine ⟨g, r, hr, hga, hgc, C.affineIsometry_image_zeroSet_eq g, ?_⟩
  exact C.affineIsometryFunctionFieldAlgEquiv_apply_squaredDistance_pair
    g a c r hga hgc

end IrreduciblePlanePolynomial

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace PachDeZeeuw.Algebraic

open MvPolynomial _root_.Polynomial


theorem isCoprime_fraction_map_of_primitive_irreducible_not_dvd
    (P Q : Polynomial XCoeff)
    (hPprim : P.IsPrimitive)
    (hPirr : Irreducible P)
    (hnot : ¬ P ∣ Q) :
    IsCoprime (P.map (algebraMap XCoeff XFrac))
      (Q.map (algebraMap XCoeff XFrac)) := by
  have hPmapIrr : Irreducible (P.map (algebraMap XCoeff XFrac)) :=
    hPprim.irreducible_iff_irreducible_map_fraction_map.mp hPirr
  rw [hPmapIrr.coprime_iff_not_dvd]
  intro hmap
  by_cases hQzero : Q = 0
  · exact hnot (hQzero ▸ dvd_zero P)
  have hcontent : Q.content ≠ 0 := by
    intro hzero
    exact hQzero (Polynomial.content_eq_zero_iff.mp hzero)
  have hcontentMapUnit :
      IsUnit (Polynomial.C (algebraMap XCoeff XFrac Q.content)) := by
    apply Polynomial.isUnit_C.mpr
    apply isUnit_iff_ne_zero.mpr
    intro hzero
    apply hcontent
    exact IsFractionRing.injective XCoeff XFrac (by simpa using hzero)
  have hmapPrimPart :
      P.map (algebraMap XCoeff XFrac) ∣ Q.primPart.map (algebraMap XCoeff XFrac) := by
    apply (IsUnit.dvd_mul_left hcontentMapUnit).mp
    rw [← Polynomial.map_C, ← Polynomial.map_mul, ← Q.eq_C_content_mul_primPart]
    exact hmap
  have hprimPart : P ∣ Q.primPart :=
    hPprim.dvd_of_fraction_map_dvd_fraction_map hmapPrimPart
  exact hnot (dvd_trans hprimPart Q.primPart_dvd)

end PachDeZeeuw.Algebraic

namespace Esgk

open MvPolynomial
open PachDeZeeuw.Algebraic


theorem headResultant_ne_zero_of_irreducible_not_dvd
    (p q : PlanePoly)
    (hpDegree : 0 < (headCurry p).natDegree)
    (hirr : Irreducible p)
    (hnot : ¬ p ∣ q) :
    headResultant p q ≠ 0 := by
  have hprimitive : (Curry0 p).IsPrimitive := by
    apply curry_isPrimitive_of_irreducible_positive_natDegree p hirr
    simpa only [Curry0, headCurry] using hpDegree
  have hcoprime :
      IsCoprime
        ((Curry0 p).map (algebraMap XCoeff XFrac))
        ((Curry0 q).map (algebraMap XCoeff XFrac)) := by
    exact isCoprime_fraction_map_of_primitive_irreducible_not_dvd
      (Curry0 p) (Curry0 q)
      hprimitive
      (by
        simpa [Curry0] using
          (hirr.map (MvPolynomial.finSuccEquiv ℝ 1).toRingEquiv))
      (by
        intro hdiv
        apply hnot
        have hdiv' := map_dvd (MvPolynomial.finSuccEquiv ℝ 1).symm hdiv
        simpa [Curry0] using hdiv')
  simpa [headResultant, headCurry, Curry0] using
    (resultant_ne_zero_of_fraction_coprime (Curry0 p) (Curry0 q) hcoprime)


end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic


theorem planeRadialQuadratic_isHomogeneous :
    MvPolynomial.IsHomogeneous planeRadialQuadratic 2 := by
  exact
    (MvPolynomial.isHomogeneous_X_pow (R := ℝ) (0 : Fin 2) 2).add
      (MvPolynomial.isHomogeneous_X_pow (R := ℝ) (1 : Fin 2) 2)


theorem planeSquaredDistancePolynomial_eq_radial_linear_constant (a : PachDeZeeuw.Algebraic.Point2) :
    planeSquaredDistancePolynomial a =
      planeRadialQuadratic -
        MvPolynomial.C (2 * a 0) * MvPolynomial.X 0 -
        MvPolynomial.C (2 * a 1) * MvPolynomial.X 1 +
        MvPolynomial.C (a 0 ^ 2 + a 1 ^ 2) := by
  simp only [planeSquaredDistancePolynomial, planeRadialQuadratic, map_add, map_mul, map_pow,
    map_ofNat]
  ring


theorem homogeneousComponent_two_planeSquaredDistancePolynomial (a : PachDeZeeuw.Algebraic.Point2) :
    MvPolynomial.homogeneousComponent 2 (planeSquaredDistancePolynomial a) =
      planeRadialQuadratic := by
  have hlinear0 :
      MvPolynomial.IsHomogeneous
        (MvPolynomial.C (2 * a 0) * MvPolynomial.X 0 : PlanePoly) 1 :=
    (MvPolynomial.isHomogeneous_X (R := ℝ) (0 : Fin 2)).C_mul _
  have hlinear1 :
      MvPolynomial.IsHomogeneous
        (MvPolynomial.C (2 * a 1) * MvPolynomial.X 1 : PlanePoly) 1 :=
    (MvPolynomial.isHomogeneous_X (R := ℝ) (1 : Fin 2)).C_mul _
  have hconstant :
      MvPolynomial.IsHomogeneous
        (MvPolynomial.C (a 0 ^ 2 + a 1 ^ 2) : PlanePoly) 0 :=
    MvPolynomial.isHomogeneous_C _ _
  rw [planeSquaredDistancePolynomial_eq_radial_linear_constant]
  rw [map_add, map_sub, map_sub]
  rw [MvPolynomial.homogeneousComponent_of_mem planeRadialQuadratic_isHomogeneous,
    MvPolynomial.homogeneousComponent_of_mem hlinear0,
    MvPolynomial.homogeneousComponent_of_mem hlinear1,
    MvPolynomial.homogeneousComponent_of_mem hconstant]
  norm_num

private theorem inline_Esgk_PlaneRadialQuadratic__totalDegree_X_sub_C_sq_le_two (a : ℝ) (k : Fin 2) :
    ((MvPolynomial.X k - MvPolynomial.C a) ^ 2 : PlanePoly).totalDegree ≤ 2 := by
  calc
    ((MvPolynomial.X k - MvPolynomial.C a) ^ 2 : PlanePoly).totalDegree ≤
        2 * (MvPolynomial.X k - MvPolynomial.C a : PlanePoly).totalDegree :=
      MvPolynomial.totalDegree_pow _ _
    _ ≤ 2 * 1 := Nat.mul_le_mul_left 2 (by
      simpa using
        (MvPolynomial.totalDegree_sub
          (MvPolynomial.X k : PlanePoly) (MvPolynomial.C a)))
    _ = 2 := by omega

 
theorem planeSquaredDistancePolynomial_totalDegree_le (a : PachDeZeeuw.Algebraic.Point2) :
    (planeSquaredDistancePolynomial a).totalDegree ≤ 2 := by
  rw [planeSquaredDistancePolynomial]
  exact (MvPolynomial.totalDegree_add _ _).trans
    (max_le (inline_Esgk_PlaneRadialQuadratic__totalDegree_X_sub_C_sq_le_two (a 0) 0)
      (inline_Esgk_PlaneRadialQuadratic__totalDegree_X_sub_C_sq_le_two (a 1) 1))

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace PachDeZeeuw.Algebraic

open MvPolynomial _root_.Polynomial


theorem curry0_natDegree_pos_of_pderiv_zero_ne
    (p : PlanePoly) (hpartial : pderiv (0 : Fin 2) p ≠ 0) :
    0 < (Curry0 p).natDegree := by
  have hdegree_ne : MvPolynomial.degreeOf (0 : Fin 2) p ≠ 0 := by
    intro hzero
    apply hpartial
    rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars]
    rw [MvPolynomial.mem_vars_iff_degreeOf_ne_zero]
    exact not_not_intro hzero
  have hcurry_degree :
      (Curry0 p).natDegree = MvPolynomial.degreeOf (0 : Fin 2) p := by
    simpa [Curry0] using
      (MvPolynomial.natDegree_finSuccEquiv (R := ℝ) (n := 1) (f := p))
  rw [hcurry_degree]
  exact Nat.pos_of_ne_zero hdegree_ne


end PachDeZeeuw.Algebraic
end

end


section
set_option autoImplicit true

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace PachDeZeeuw.Algebraic

open MvPolynomial


theorem sepPoly_eval (p q : ℝ × ℝ) (s : ℝ) :
    (sepPoly p q).eval s = (p.1 - q.1) - s * (p.2 - q.2) := by
  simp only [sepPoly, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_X]
  ring


theorem sepPoly_ne_zero {p q : ℝ × ℝ} (hpq : p ≠ q) : sepPoly p q ≠ 0 := by
  intro hzero
  by_cases hy : p.2 = q.2
  ·  
    have hx : p.1 ≠ q.1 := by
      intro hx
      exact hpq (Prod.ext hx hy)
    have hcoeff : (sepPoly p q).coeff 0 = p.1 - q.1 := by
      simp only [sepPoly, hy, sub_self, map_zero, zero_mul, sub_zero]
      rw [Polynomial.coeff_C, if_pos rfl]
    rw [hzero, Polynomial.coeff_zero] at hcoeff
    exact (sub_ne_zero.mpr hx) hcoeff.symm
  ·  
    have hcoeff : (sepPoly p q).coeff 1 = -(p.2 - q.2) := by
      rw [sepPoly, Polynomial.coeff_sub, Polynomial.coeff_C, if_neg (by norm_num),
        Polynomial.coeff_C_mul, Polynomial.coeff_X_one, mul_one, zero_sub]
    rw [hzero, Polynomial.coeff_zero] at hcoeff
    have : p.2 - q.2 = 0 := by linarith [neg_eq_zero.mp hcoeff.symm]
    exact (sub_ne_zero.mpr hy) this


theorem exists_good_shear
    (Γ : Finset PlanePoly) (P : Finset (ℝ × ℝ)) (d : ℕ)
    (hirr : ∀ h ∈ Γ, Irreducible h)
    (hdeg : ∀ h ∈ Γ, h.totalDegree ≤ d)
    (hpos : ∀ h ∈ Γ, 1 ≤ h.totalDegree) :
    ∃ s : ℝ,
      (∀ h ∈ Γ, MvPolynomial.pderiv (1 : Fin 2) (shearPoly s h) ≠ 0) ∧
      (∀ h ∈ Γ, (shearPoly s h).totalDegree ≤ d) ∧
      (∀ h ∈ Γ, Irreducible (shearPoly s h)) ∧
      Set.InjOn (fun p => (shearPoint s p).1) ↑P := by
  classical
   
  set B₁ : Set ℝ := ⋃ h ∈ Γ, {s : ℝ | MvPolynomial.pderiv (1 : Fin 2) (shearPoly s h) = 0}
    with hB₁
  have hB₁_fin : B₁.Finite := by
    rw [hB₁]
    refine Set.Finite.biUnion (Finset.finite_toSet Γ) ?_
    intro h hh
    exact partialY_shearPoly_finite_bad h (hpos h hh)
   
  set B₂ : Set ℝ := ⋃ pq ∈ P.offDiag, {s : ℝ | (sepPoly pq.1 pq.2).IsRoot s} with hB₂
  have hB₂_fin : B₂.Finite := by
    rw [hB₂]
    refine Set.Finite.biUnion (Finset.finite_toSet _) ?_
    intro pq hpq
    have hne : pq.1 ≠ pq.2 := (Finset.mem_offDiag.mp (Finset.mem_coe.mp hpq)).2.2
    exact Polynomial.finite_setOfPred_isRoot (sepPoly_ne_zero hne)
   
  obtain ⟨s, hs⟩ := (hB₁_fin.union hB₂_fin).exists_notMem
  rw [Set.mem_union, not_or] at hs
  obtain ⟨hs₁, hs₂⟩ := hs
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  ·  
    intro h hh hpd
    apply hs₁
    rw [hB₁, Set.mem_iUnion₂]
    exact ⟨h, hh, hpd⟩
  ·  
    intro h hh
    exact (shearPoly_totalDegree_le s h).trans (hdeg h hh)
  ·  
    intro h hh
    exact (irreducible_shearPoly_iff s h).mpr (hirr h hh)
  ·  
    intro p hp q hq hpqeq
    by_contra hpq
     
    apply hs₂
    rw [hB₂, Set.mem_iUnion₂]
    refine ⟨(p, q), Finset.mem_offDiag.mpr ⟨Finset.mem_coe.mp hp, Finset.mem_coe.mp hq, hpq⟩, ?_⟩
    simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def, sepPoly_eval]
     
    simp only [shearPoint_apply] at hpqeq
    linarith [hpqeq]

end PachDeZeeuw.Algebraic

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic _root_.Polynomial


@[simp]
theorem affineLineParam_apply (x v : PachDeZeeuw.Algebraic.Point2) (t : ℝ) (i : Fin 2) :
    affineLineParam x v t i = x i + t * v i := by
  simp [affineLineParam]


private theorem inline_Esgk_AffineLinePolynomialRestriction__eval_affineLineCoordinatePolynomial
    (x v : PachDeZeeuw.Algebraic.Point2) (i : Fin 2) (t : ℝ) :
    eval t (bundle_Esgk_AffineLinePolynomialRestriction_affineLineCoordinatePolynomial x v i) = affineLineParam x v t i := by
  rw [affineLineParam_apply]
  simp [bundle_Esgk_AffineLinePolynomialRestriction_affineLineCoordinatePolynomial]
  ring

private theorem inline_Esgk_AffineLinePolynomialRestriction__natDegree_affineLineCoordinatePolynomial_le
    (x v : PachDeZeeuw.Algebraic.Point2) (i : Fin 2) :
    (bundle_Esgk_AffineLinePolynomialRestriction_affineLineCoordinatePolynomial x v i).natDegree ≤ 1 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  rw [bundle_Esgk_AffineLinePolynomialRestriction_affineLineCoordinatePolynomial, Polynomial.coeff_add,
    Polynomial.coeff_C_of_ne_zero hn0, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_of_ne_one hn1]
  simp


private theorem inline_Esgk_AffineLinePolynomialRestriction__natDegree_affineLineRestrictedMonomial_le
    (x v : PachDeZeeuw.Algebraic.Point2) (i j : ℕ) (a : ℝ) :
    (bundle_Esgk_AffineLinePolynomialRestriction_affineLineRestrictedMonomial x v i j a).natDegree ≤ i + j := by
  have hcoeff : (C a : Polynomial ℝ).natDegree ≤ 0 := by
    simp
  have hfirst :
      (bundle_Esgk_AffineLinePolynomialRestriction_affineLineCoordinatePolynomial x v 0 ^ i).natDegree ≤ i := by
    simpa using Polynomial.natDegree_pow_le_of_le i
      (inline_Esgk_AffineLinePolynomialRestriction__natDegree_affineLineCoordinatePolynomial_le x v 0)
  have hsecond :
      (bundle_Esgk_AffineLinePolynomialRestriction_affineLineCoordinatePolynomial x v 1 ^ j).natDegree ≤ j := by
    simpa using Polynomial.natDegree_pow_le_of_le j
      (inline_Esgk_AffineLinePolynomialRestriction__natDegree_affineLineCoordinatePolynomial_le x v 1)
  have hfirstProduct :
      (C a * bundle_Esgk_AffineLinePolynomialRestriction_affineLineCoordinatePolynomial x v 0 ^ i).natDegree ≤ i := by
    simpa using Polynomial.natDegree_mul_le_of_le hcoeff hfirst
  exact Polynomial.natDegree_mul_le_of_le hfirstProduct hsecond

private theorem inline_Esgk_AffineLinePolynomialRestriction__eval_affineLineRestrictedMonomial
    (x v : PachDeZeeuw.Algebraic.Point2) (t : ℝ) (i j : ℕ) (a : ℝ) :
    eval t (bundle_Esgk_AffineLinePolynomialRestriction_affineLineRestrictedMonomial x v i j a) =
      a * (affineLineParam x v t 0) ^ i * (affineLineParam x v t 1) ^ j := by
  simp [bundle_Esgk_AffineLinePolynomialRestriction_affineLineRestrictedMonomial, inline_Esgk_AffineLinePolynomialRestriction__eval_affineLineCoordinatePolynomial]


theorem natDegree_affineLinePolynomialRestriction_le
    (p : PlanePoly) (x v : PachDeZeeuw.Algebraic.Point2) (d : ℕ) (hdegree : p.totalDegree ≤ d) :
    (affineLinePolynomialRestriction p x v).natDegree ≤ d := by
  rw [affineLinePolynomialRestriction, MvPolynomial.sum_def]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro exponent hexponent
  apply (inline_Esgk_AffineLinePolynomialRestriction__natDegree_affineLineRestrictedMonomial_le x v
    (exponent 0) (exponent 1) (p.coeff exponent)).trans
  have htotal := (MvPolynomial.le_totalDegree hexponent).trans hdegree
  simpa [Finsupp.sum_fintype, Fin.sum_univ_two] using htotal


theorem eval_affineLinePolynomialRestriction
    (p : PlanePoly) (x v : PachDeZeeuw.Algebraic.Point2) (t : ℝ) :
    eval t (affineLinePolynomialRestriction p x v) =
      MvPolynomial.eval (fun i ↦ affineLineParam x v t i) p := by
  rw [affineLinePolynomialRestriction, MvPolynomial.sum_def,
    Polynomial.eval_finsetSum, MvPolynomial.eval_eq']
  apply Finset.sum_congr rfl
  intro exponent hexponent
  rw [inline_Esgk_AffineLinePolynomialRestriction__eval_affineLineRestrictedMonomial]
  simp [Fin.prod_univ_two, mul_assoc]


theorem exists_affineLineParam_eq_of_mem_affineLinePolynomial_zeroSet
    (x : PachDeZeeuw.Algebraic.Point2) {v z : PachDeZeeuw.Algebraic.Point2} (hv : v ≠ 0)
    (hz : z ∈ PlaneCurveZeroSet (affineLinePolynomial x v)) :
    ∃ t : ℝ, affineLineParam x v t = z := by
  rw [mem_PlaneCurveZeroSet, affineLinePolynomial_eval] at hz
  by_cases hv0 : v 0 = 0
  · have hv1 : v 1 ≠ 0 := by
      intro hv1
      apply hv
      ext i
      fin_cases i
      · exact hv0
      · exact hv1
    have hxprod : v 1 * (z 0 - x 0) = 0 := by
      simpa [hv0] using hz
    have hx : x 0 = z 0 := by
      have := (mul_eq_zero.mp hxprod).resolve_left hv1
      linarith
    let t := (z 1 - x 1) / v 1
    have ht0 : affineLineParam x v t 0 = z 0 := by
      simp [t, hv0, hx]
    have ht1 : affineLineParam x v t 1 = z 1 := by
      rw [affineLineParam_apply]
      dsimp [t]
      field_simp [hv1]
      ring
    refine ⟨t, ?_⟩
    ext i
    fin_cases i
    · exact ht0
    · exact ht1
  · let t := (z 0 - x 0) / v 0
    have ht0 : affineLineParam x v t 0 = z 0 := by
      rw [affineLineParam_apply]
      dsimp [t]
      field_simp [hv0]
      ring
    have ht1 : affineLineParam x v t 1 = z 1 := by
      rw [affineLineParam_apply]
      dsimp [t]
      field_simp [hv0]
      ring_nf at hz ⊢
      linarith
    refine ⟨t, ?_⟩
    ext i
    fin_cases i
    · exact ht0
    · exact ht1


theorem affineLinePolynomialRestriction_ne_zero_of_not_subset
    (p : PlanePoly) (x : PachDeZeeuw.Algebraic.Point2) {v : PachDeZeeuw.Algebraic.Point2} (hv : v ≠ 0)
    (hnot : ¬ PlaneCurveZeroSet (affineLinePolynomial x v) ⊆ PlaneCurveZeroSet p) :
    affineLinePolynomialRestriction p x v ≠ 0 := by
  intro hrestriction
  apply hnot
  intro z hz
  rw [mem_PlaneCurveZeroSet]
  obtain ⟨t, rfl⟩ :=
    exists_affineLineParam_eq_of_mem_affineLinePolynomial_zeroSet x hv hz
  have heval := eval_affineLinePolynomialRestriction p x v t
  rw [hrestriction] at heval
  simpa using heval.symm


theorem finite_affineLine_zeroSet_card_le_of_not_subset
    (p : PlanePoly) (x : PachDeZeeuw.Algebraic.Point2) {v : PachDeZeeuw.Algebraic.Point2} (d : ℕ) (S : Finset PachDeZeeuw.Algebraic.Point2)
    (hv : v ≠ 0) (hdegree : p.totalDegree ≤ d)
    (hzero : ∀ z ∈ S, MvPolynomial.eval (fun i ↦ z i) p = 0)
    (hline : ∀ z ∈ S, z ∈ PlaneCurveZeroSet (affineLinePolynomial x v))
    (hnot : ¬ PlaneCurveZeroSet (affineLinePolynomial x v) ⊆ PlaneCurveZeroSet p) :
    S.card ≤ d := by
  let H := affineLinePolynomialRestriction p x v
  have hrestriction : H ≠ 0 := by
    exact affineLinePolynomialRestriction_ne_zero_of_not_subset p x hv hnot
  have hdegreeH : H.natDegree ≤ d := by
    exact natDegree_affineLinePolynomialRestriction_le p x v d hdegree
  apply le_trans
    (card_le_natDegree_of_parametrized_roots S H (affineLineParam x v) ?_)
    hdegreeH
  intro z hz
  obtain ⟨t, ht⟩ :=
    exists_affineLineParam_eq_of_mem_affineLinePolynomial_zeroSet x hv (hline z hz)
  refine ⟨t, ?_, ht⟩
  rw [Multiset.mem_toFinset]
  apply (Polynomial.mem_roots hrestriction).2
  rw [Polynomial.IsRoot.def]
  rw [show H = affineLinePolynomialRestriction p x v by rfl]
  rw [eval_affineLinePolynomialRestriction]
  simpa [ht] using hzero z hz

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

variable {n : ℕ}


theorem planeRadialQuadratic_ne_zero : planeRadialQuadratic ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval (fun i : Fin 2 ↦ if i = 0 then (1 : ℝ) else 0)) hzero
  simp [planeRadialQuadratic] at heval


end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

namespace IrreduciblePlanePolynomial

variable {F : Type*} [Field F]


@[simp]
theorem affineNormalizationLift_coe
    (C : IrreduciblePlanePolynomial F) (a : C.CoordinateRing) :
    (C.affineNormalizationLift a : C.FunctionField) =
      algebraMap C.CoordinateRing C.FunctionField a := by
  exact IsScalarTower.algebraMap_apply
    C.CoordinateRing C.affineNormalizationRing C.FunctionField a


theorem affineNormalizationRingAlgEquivOfFunctionFieldAlgEquiv_apply_lift
    (C : IrreduciblePlanePolynomial F)
    (T : C.FunctionField ≃ₐ[F] C.FunctionField)
    (hforward : ∀ a : C.CoordinateRing,
      IsIntegral C.CoordinateRing
        (T (algebraMap C.CoordinateRing C.FunctionField a)))
    (hbackward : ∀ a : C.CoordinateRing,
      IsIntegral C.CoordinateRing
        (T.symm (algebraMap C.CoordinateRing C.FunctionField a)))
    {a b : C.CoordinateRing}
    (hT : T (algebraMap C.CoordinateRing C.FunctionField b) =
      algebraMap C.CoordinateRing C.FunctionField a) :
    C.affineNormalizationRingAlgEquivOfFunctionFieldAlgEquiv
          T hforward hbackward (C.affineNormalizationLift b) =
        C.affineNormalizationLift a := by
  apply Subtype.ext
  simpa using hT

end IrreduciblePlanePolynomial

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

namespace IrreduciblePlanePolynomial


theorem normalizedDistanceImageFunctionFieldAlgEquiv_apply_coordinates
    (C : IrreduciblePlanePolynomial ℝ)
    (g : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) {r : ℝ} (hr : r ≠ 0)
    (hns :
      xAxisReflectionPoint ''
          PlaneCurveZeroSet (C.affineIsometryTransport g).polynomial ≠
        PlaneCurveZeroSet (C.affineIsometryTransport g).polynomial)
    (a c : PachDeZeeuw.Algebraic.Point2)
    (hga : g a = xAxisPoint (-r))
    (hgc : g c = xAxisPoint r) :
    C.normalizedDistanceImageFunctionFieldAlgEquiv g hr hns
          ((C.affineIsometryTransport g).distanceImageCoordinate r 0) =
        C.squaredDistanceFunctionAt a ∧
      C.normalizedDistanceImageFunctionFieldAlgEquiv g hr hns
          ((C.affineIsometryTransport g).distanceImageCoordinate r 1) =
        C.squaredDistanceFunctionAt c := by
  have hpair :=
    C.affineIsometryFunctionFieldAlgEquiv_apply_squaredDistance_pair
      g a c r hga hgc
  constructor
  · apply (C.affineIsometryFunctionFieldAlgEquiv g).injective
    rw [hpair.1]
    simp [normalizedDistanceImageFunctionFieldAlgEquiv]
  · apply (C.affineIsometryFunctionFieldAlgEquiv g).injective
    rw [hpair.2]
    simp [normalizedDistanceImageFunctionFieldAlgEquiv]

end IrreduciblePlanePolynomial

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

namespace IrreduciblePlanePolynomial

private theorem inline_Esgk_IrreduciblePlaneTwoPairCoordinateIntegrality__ringHom_map_add_sq_add_sq
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (x s y : R) :
    f ((x + s) ^ 2 + y ^ 2) = (f x + f s) ^ 2 + (f y) ^ 2 := by
  rw [map_add, map_pow, map_add, map_pow]

private theorem inline_Esgk_IrreduciblePlaneTwoPairCoordinateIntegrality__ringHom_map_sub_sq_add_sq
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (x s y : R) :
    f ((x - s) ^ 2 + y ^ 2) = (f x - f s) ^ 2 + (f y) ^ 2 := by
  rw [map_add, map_pow, map_sub, map_pow]


theorem adjoin_affineNormalizedCoordinateClass_range_eq_top
    (C : IrreduciblePlanePolynomial ℝ) (g : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) :
    Algebra.adjoin ℝ (Set.range (C.affineNormalizedCoordinateClass g)) = ⊤ := by
  let e := C.affineIsometryCoordinateRingAlgEquiv g
  have himage :
      e.toAlgHom '' Set.range (C.affineNormalizedCoordinateClass g) =
        Set.range (C.affineIsometryTransport g).coordinateClass := by
    ext z
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (e.apply_symm_apply _).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨C.affineNormalizedCoordinateClass g i, ⟨i, rfl⟩,
        by
          change e (e.symm
            ((C.affineIsometryTransport g).coordinateClass i)) = _
          exact e.apply_symm_apply _⟩
  apply (Subalgebra.map_injective
    (f := e.toAlgHom) e.injective)
  rw [AlgHom.map_adjoin, Algebra.map_top]
  rw [himage]
  have hrange : e.toAlgHom.range = ⊤ :=
    (AlgHom.range_eq_top e.toAlgHom).2 e.surjective
  rw [hrange]
  exact (C.affineIsometryTransport g).adjoin_coordinateClass_range_eq_top


theorem affineNormalizedCoordinate_eq_algebraMap
    (C : IrreduciblePlanePolynomial ℝ) (g : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2)
    (i : Fin 2) :
    C.affineNormalizedCoordinate g i =
      algebraMap C.CoordinateRing C.FunctionField
        (C.affineNormalizedCoordinateClass g i) := by
  change
    (C.functionFieldAlgEquivTransport (planeAffinePolynomialEquiv g.symm)).symm
        (algebraMap (C.affineIsometryTransport g).CoordinateRing
          (C.affineIsometryTransport g).FunctionField
          ((C.affineIsometryTransport g).coordinateClass i)) =
      algebraMap C.CoordinateRing C.FunctionField
        ((C.coordinateRingAlgEquivTransport
          (planeAffinePolynomialEquiv g.symm)).symm
          ((C.affineIsometryTransport g).coordinateClass i))
  exact C.functionFieldAlgEquivTransport_symm_apply_algebraMap
    (planeAffinePolynomialEquiv g.symm)
    ((C.affineIsometryTransport g).coordinateClass i)


private theorem inline_Esgk_IrreduciblePlaneTwoPairCoordinateIntegrality__squaredDistanceFunctionAt_eq_normalized_left
    (C : IrreduciblePlanePolynomial ℝ) (g : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2)
    (a : PachDeZeeuw.Algebraic.Point2) (r : ℝ) (hga : g a = xAxisPoint (-r)) :
    C.squaredDistanceFunctionAt a =
      (C.affineNormalizedCoordinate g 0 + algebraMap ℝ C.FunctionField r) ^ 2 +
        C.affineNormalizedCoordinate g 1 ^ 2 := by
  apply (C.affineIsometryFunctionFieldAlgEquiv g).injective
  rw [C.affineIsometryFunctionFieldAlgEquiv_apply_squaredDistanceFunctionAt,
    hga, (C.affineIsometryTransport g).squaredDistanceFunctionAt_xAxisPoint_neg]
  change _ =
    (C.affineIsometryFunctionFieldAlgEquiv g).toRingEquiv.toRingHom
      ((C.affineNormalizedCoordinate g 0 +
        algebraMap ℝ C.FunctionField r) ^ 2 +
        C.affineNormalizedCoordinate g 1 ^ 2)
  have hcoord (i : Fin 2) :
      (C.affineIsometryFunctionFieldAlgEquiv g).toRingEquiv.toRingHom
          (C.affineNormalizedCoordinate g i) =
        (C.affineIsometryTransport g).coordinate i :=
    (C.affineIsometryFunctionFieldAlgEquiv g).apply_symm_apply _
  have hscalar :
      (C.affineIsometryFunctionFieldAlgEquiv g).toRingEquiv.toRingHom
          (algebraMap ℝ C.FunctionField r) =
        algebraMap ℝ (C.affineIsometryTransport g).FunctionField r :=
    (C.affineIsometryFunctionFieldAlgEquiv g).commutes r
  rw [inline_Esgk_IrreduciblePlaneTwoPairCoordinateIntegrality__ringHom_map_add_sq_add_sq
      (C.affineIsometryFunctionFieldAlgEquiv g).toRingEquiv.toRingHom,
    hcoord 0, hcoord 1, hscalar]
  change
    algebraMap (C.affineIsometryTransport g).CoordinateRing
        (C.affineIsometryTransport g).FunctionField
        (((C.affineIsometryTransport g).coordinateClass 0 +
          algebraMap ℝ (C.affineIsometryTransport g).CoordinateRing r) ^ 2 +
          (C.affineIsometryTransport g).coordinateClass 1 ^ 2) = _
  rw [inline_Esgk_IrreduciblePlaneTwoPairCoordinateIntegrality__ringHom_map_add_sq_add_sq
      (algebraMap (C.affineIsometryTransport g).CoordinateRing
        (C.affineIsometryTransport g).FunctionField),
    IsScalarTower.algebraMap_apply ℝ
      (C.affineIsometryTransport g).CoordinateRing
      (C.affineIsometryTransport g).FunctionField]
  rfl

private theorem inline_Esgk_IrreduciblePlaneTwoPairCoordinateIntegrality__squaredDistanceFunctionAt_eq_normalized_right
    (C : IrreduciblePlanePolynomial ℝ) (g : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2)
    (a : PachDeZeeuw.Algebraic.Point2) (r : ℝ) (hga : g a = xAxisPoint r) :
    C.squaredDistanceFunctionAt a =
      (C.affineNormalizedCoordinate g 0 - algebraMap ℝ C.FunctionField r) ^ 2 +
        C.affineNormalizedCoordinate g 1 ^ 2 := by
  apply (C.affineIsometryFunctionFieldAlgEquiv g).injective
  rw [C.affineIsometryFunctionFieldAlgEquiv_apply_squaredDistanceFunctionAt,
    hga, (C.affineIsometryTransport g).squaredDistanceFunctionAt_xAxisPoint]
  change _ =
    (C.affineIsometryFunctionFieldAlgEquiv g).toRingEquiv.toRingHom
      ((C.affineNormalizedCoordinate g 0 -
        algebraMap ℝ C.FunctionField r) ^ 2 +
        C.affineNormalizedCoordinate g 1 ^ 2)
  have hcoord (i : Fin 2) :
      (C.affineIsometryFunctionFieldAlgEquiv g).toRingEquiv.toRingHom
          (C.affineNormalizedCoordinate g i) =
        (C.affineIsometryTransport g).coordinate i :=
    (C.affineIsometryFunctionFieldAlgEquiv g).apply_symm_apply _
  have hscalar :
      (C.affineIsometryFunctionFieldAlgEquiv g).toRingEquiv.toRingHom
          (algebraMap ℝ C.FunctionField r) =
        algebraMap ℝ (C.affineIsometryTransport g).FunctionField r :=
    (C.affineIsometryFunctionFieldAlgEquiv g).commutes r
  rw [inline_Esgk_IrreduciblePlaneTwoPairCoordinateIntegrality__ringHom_map_sub_sq_add_sq
      (C.affineIsometryFunctionFieldAlgEquiv g).toRingEquiv.toRingHom,
    hcoord 0, hcoord 1, hscalar]
  change
    algebraMap (C.affineIsometryTransport g).CoordinateRing
        (C.affineIsometryTransport g).FunctionField
        (((C.affineIsometryTransport g).coordinateClass 0 -
          algebraMap ℝ (C.affineIsometryTransport g).CoordinateRing r) ^ 2 +
          (C.affineIsometryTransport g).coordinateClass 1 ^ 2) = _
  rw [inline_Esgk_IrreduciblePlaneTwoPairCoordinateIntegrality__ringHom_map_sub_sq_add_sq
      (algebraMap (C.affineIsometryTransport g).CoordinateRing
        (C.affineIsometryTransport g).FunctionField),
    IsScalarTower.algebraMap_apply ℝ
      (C.affineIsometryTransport g).CoordinateRing
      (C.affineIsometryTransport g).FunctionField]
  rfl

set_option maxHeartbeats 1000000 in
 

theorem affineNormalizedCoordinate_forward_formulas
    (C : IrreduciblePlanePolynomial ℝ)
    (T : C.FunctionField ≃ₐ[ℝ] C.FunctionField)
    (g₁ g₂ : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) (r₁ r₂ : ℝ) (hr₂ : r₂ ≠ 0)
    (a c b d : PachDeZeeuw.Algebraic.Point2)
    (hg₁a : g₁ a = xAxisPoint (-r₁)) (hg₁c : g₁ c = xAxisPoint r₁)
    (hg₂b : g₂ b = xAxisPoint (-r₂)) (hg₂d : g₂ d = xAxisPoint r₂)
    (hTb : T (C.squaredDistanceFunctionAt b) = C.squaredDistanceFunctionAt a)
    (hTd : T (C.squaredDistanceFunctionAt d) = C.squaredDistanceFunctionAt c) :
    T (C.affineNormalizedCoordinate g₂ 0) =
        algebraMap ℝ C.FunctionField (r₁ / r₂) *
          C.affineNormalizedCoordinate g₁ 0 ∧
      T (C.affineNormalizedCoordinate g₂ 1) ^ 2 =
        C.affineNormalizedCoordinate g₁ 1 ^ 2 +
          (1 - algebraMap ℝ C.FunctionField (r₁ / r₂) ^ 2) *
            C.affineNormalizedCoordinate g₁ 0 ^ 2 +
          algebraMap ℝ C.FunctionField (r₁ ^ 2 - r₂ ^ 2) := by
  let x₁ := C.affineNormalizedCoordinate g₁ 0
  let y₁ := C.affineNormalizedCoordinate g₁ 1
  let x₂ := C.affineNormalizedCoordinate g₂ 0
  let y₂ := C.affineNormalizedCoordinate g₂ 1
  let s : ℝ →+* C.FunctionField := algebraMap ℝ C.FunctionField
  have hleft : (T x₂ + s r₂) ^ 2 + (T y₂) ^ 2 =
      (x₁ + s r₁) ^ 2 + y₁ ^ 2 := by
    calc
      _ = T ((x₂ + s r₂) ^ 2 + y₂ ^ 2) := by
        have hmap := inline_Esgk_IrreduciblePlaneTwoPairCoordinateIntegrality__ringHom_map_add_sq_add_sq
          T.toRingEquiv.toRingHom x₂ (s r₂) y₂
        have hs : T.toRingEquiv.toRingHom (s r₂) = s r₂ := T.commutes r₂
        rw [hs] at hmap
        exact hmap.symm
      _ = T (C.squaredDistanceFunctionAt b) := by
        rw [inline_Esgk_IrreduciblePlaneTwoPairCoordinateIntegrality__squaredDistanceFunctionAt_eq_normalized_left C g₂ b r₂ hg₂b]
      _ = C.squaredDistanceFunctionAt a := hTb
      _ = _ := inline_Esgk_IrreduciblePlaneTwoPairCoordinateIntegrality__squaredDistanceFunctionAt_eq_normalized_left
        C g₁ a r₁ hg₁a
  have hright : (T x₂ - s r₂) ^ 2 + (T y₂) ^ 2 =
      (x₁ - s r₁) ^ 2 + y₁ ^ 2 := by
    calc
      _ = T ((x₂ - s r₂) ^ 2 + y₂ ^ 2) := by
        have hmap := inline_Esgk_IrreduciblePlaneTwoPairCoordinateIntegrality__ringHom_map_sub_sq_add_sq
          T.toRingEquiv.toRingHom x₂ (s r₂) y₂
        have hs : T.toRingEquiv.toRingHom (s r₂) = s r₂ := T.commutes r₂
        rw [hs] at hmap
        exact hmap.symm
      _ = T (C.squaredDistanceFunctionAt d) := by
        rw [inline_Esgk_IrreduciblePlaneTwoPairCoordinateIntegrality__squaredDistanceFunctionAt_eq_normalized_right C g₂ d r₂ hg₂d]
      _ = C.squaredDistanceFunctionAt c := hTd
      _ = _ := inline_Esgk_IrreduciblePlaneTwoPairCoordinateIntegrality__squaredDistanceFunctionAt_eq_normalized_right
        C g₁ c r₁ hg₁c
  have hsr₂ : s r₂ ≠ 0 := by simpa using s.injective.ne hr₂
  have hsdiv : s (r₁ / r₂) = s r₁ / s r₂ := map_div₀ s r₁ r₂
  have hcross : T x₂ * s r₂ = x₁ * s r₁ := by
    have hfour : (4 : C.FunctionField) ≠ 0 := by
      rw [← map_ofNat s 4]
      simp
    apply mul_left_cancel₀ hfour
    linear_combination hleft - hright
  have hx : T x₂ = s (r₁ / r₂) * x₁ := by
    rw [hsdiv]
    field_simp [hsr₂]
    simpa [mul_comm] using hcross
  refine ⟨hx, ?_⟩
  rw [hx] at hleft
  have hsdiff : s (r₁ ^ 2 - r₂ ^ 2) = s (r₁ ^ 2) - s (r₂ ^ 2) :=
    map_sub s _ _
  have hspow₁ : s (r₁ ^ 2) = (s r₁) ^ 2 := map_pow s r₁ 2
  have hspow₂ : s (r₂ ^ 2) = (s r₂) ^ 2 := map_pow s r₂ 2
  change (T y₂) ^ 2 = y₁ ^ 2 +
    (1 - s (r₁ / r₂) ^ 2) * x₁ ^ 2 + s (r₁ ^ 2 - r₂ ^ 2)
  rw [hsdiv] at hleft ⊢
  rw [hsdiff, hspow₁, hspow₂]
  field_simp [hsr₂] at hleft ⊢
  linear_combination hleft


set_option maxHeartbeats 1000000 in
 

theorem isIntegral_affineNormalizedCoordinate_forward
    (C : IrreduciblePlanePolynomial ℝ)
    (T : C.FunctionField ≃ₐ[ℝ] C.FunctionField)
    (g₁ g₂ : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) (r₁ r₂ : ℝ) (hr₂ : r₂ ≠ 0)
    (a c b d : PachDeZeeuw.Algebraic.Point2)
    (hg₁a : g₁ a = xAxisPoint (-r₁)) (hg₁c : g₁ c = xAxisPoint r₁)
    (hg₂b : g₂ b = xAxisPoint (-r₂)) (hg₂d : g₂ d = xAxisPoint r₂)
    (hTb : T (C.squaredDistanceFunctionAt b) = C.squaredDistanceFunctionAt a)
    (hTd : T (C.squaredDistanceFunctionAt d) = C.squaredDistanceFunctionAt c)
    (i : Fin 2) :
    IsIntegral C.CoordinateRing
      (T (algebraMap C.CoordinateRing C.FunctionField
        (C.affineNormalizedCoordinateClass g₂ i))) := by
  have hform := C.affineNormalizedCoordinate_forward_formulas T
    g₁ g₂ r₁ r₂ hr₂ a c b d hg₁a hg₁c hg₂b hg₂d hTb hTd
  have hcoord (g : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) (j : Fin 2) :
      IsIntegral C.CoordinateRing (C.affineNormalizedCoordinate g j) := by
    rw [C.affineNormalizedCoordinate_eq_algebraMap]
    exact isIntegral_algebraMap
  have hscalar (q : ℝ) : IsIntegral C.CoordinateRing
      (algebraMap ℝ C.FunctionField q) := by
    rw [IsScalarTower.algebraMap_apply ℝ C.CoordinateRing C.FunctionField]
    exact isIntegral_algebraMap
  rw [← C.affineNormalizedCoordinate_eq_algebraMap]
  fin_cases i
  · change IsIntegral C.CoordinateRing
      (T (C.affineNormalizedCoordinate g₂ 0))
    rw [hform.1]
    exact (hscalar _).mul (hcoord g₁ 0)
  · change IsIntegral C.CoordinateRing
      (T (C.affineNormalizedCoordinate g₂ 1))
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [hform.2]
    exact (((hcoord g₁ 1).pow 2).add
      ((isIntegral_one.sub ((hscalar (r₁ / r₂)).pow 2)).mul
        ((hcoord g₁ 0).pow 2))).add (hscalar (r₁ ^ 2 - r₂ ^ 2))

set_option maxHeartbeats 1000000 in
 

theorem isIntegral_apply_of_twoPair_normalizedDistance
    (C : IrreduciblePlanePolynomial ℝ)
    (T : C.FunctionField ≃ₐ[ℝ] C.FunctionField)
    (g₁ g₂ : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) (r₁ r₂ : ℝ) (hr₂ : r₂ ≠ 0)
    (a c b d : PachDeZeeuw.Algebraic.Point2)
    (hg₁a : g₁ a = xAxisPoint (-r₁)) (hg₁c : g₁ c = xAxisPoint r₁)
    (hg₂b : g₂ b = xAxisPoint (-r₂)) (hg₂d : g₂ d = xAxisPoint r₂)
    (hTb : T (C.squaredDistanceFunctionAt b) = C.squaredDistanceFunctionAt a)
    (hTd : T (C.squaredDistanceFunctionAt d) = C.squaredDistanceFunctionAt c) :
    ∀ z : C.CoordinateRing, IsIntegral C.CoordinateRing
      (T (algebraMap C.CoordinateRing C.FunctionField z)) := by
  apply C.isIntegral_algEquiv_apply_of_finite_generator_range T
    (C.affineNormalizedCoordinateClass g₂)
    (C.adjoin_affineNormalizedCoordinateClass_range_eq_top g₂)
  exact C.isIntegral_affineNormalizedCoordinate_forward T
    g₁ g₂ r₁ r₂ hr₂ a c b d hg₁a hg₁c hg₂b hg₂d hTb hTd

set_option maxHeartbeats 1000000 in
 

theorem isIntegral_symm_apply_of_twoPair_normalizedDistance
    (C : IrreduciblePlanePolynomial ℝ)
    (T : C.FunctionField ≃ₐ[ℝ] C.FunctionField)
    (g₁ g₂ : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) (r₁ r₂ : ℝ) (hr₁ : r₁ ≠ 0)
    (a c b d : PachDeZeeuw.Algebraic.Point2)
    (hg₁a : g₁ a = xAxisPoint (-r₁)) (hg₁c : g₁ c = xAxisPoint r₁)
    (hg₂b : g₂ b = xAxisPoint (-r₂)) (hg₂d : g₂ d = xAxisPoint r₂)
    (hTb : T (C.squaredDistanceFunctionAt b) = C.squaredDistanceFunctionAt a)
    (hTd : T (C.squaredDistanceFunctionAt d) = C.squaredDistanceFunctionAt c) :
    ∀ z : C.CoordinateRing, IsIntegral C.CoordinateRing
      (T.symm (algebraMap C.CoordinateRing C.FunctionField z)) := by
  have hTsa : T.symm (C.squaredDistanceFunctionAt a) =
      C.squaredDistanceFunctionAt b := by
    rw [← hTb, T.symm_apply_apply]
  have hTsc : T.symm (C.squaredDistanceFunctionAt c) =
      C.squaredDistanceFunctionAt d := by
    rw [← hTd, T.symm_apply_apply]
  exact C.isIntegral_apply_of_twoPair_normalizedDistance T.symm
    g₂ g₁ r₂ r₁ hr₁ b d a c hg₂b hg₂d hg₁a hg₁c hTsa hTsc

end IrreduciblePlanePolynomial

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic


@[simp]
theorem affineCircularChart_X_zero (c : ℂ) :
    affineCircularChart c (MvPolynomial.X 0) = 1 := by
  simp [affineCircularChart]

@[simp]
theorem affineCircularChart_X_one (c : ℂ) :
    affineCircularChart c (MvPolynomial.X 1) = MvPolynomial.C c + circularChartU := by
  simp [affineCircularChart]

@[simp]
theorem projectiveCircularChart_X_zero (c : ℂ) :
    projectiveCircularChart c (MvPolynomial.X 0) = 1 := by
  simp [projectiveCircularChart]

@[simp]
theorem projectiveCircularChart_X_one (c : ℂ) :
    projectiveCircularChart c (MvPolynomial.X 1) = MvPolynomial.C c + circularChartU := by
  simp [projectiveCircularChart]

@[simp]
theorem projectiveCircularChart_X_two (c : ℂ) :
    projectiveCircularChart c (MvPolynomial.X 2) = circularChartZ := by
  simp [projectiveCircularChart]


theorem projectiveCircularChart_realPlanePolynomialProjectiveEmbedding
    (c : ℂ) (p : PlanePoly) :
    projectiveCircularChart c (realPlanePolynomialProjectiveEmbedding p) =
      affineCircularChart c p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [realPlanePolynomialProjectiveEmbedding, complexPlanePolynomialEmbedding,
      realToComplexPlanePolynomial, affineCircularChart, projectiveCircularChart]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, hp]
      fin_cases i <;>
        simp [realPlanePolynomialProjectiveEmbedding, complexPlanePolynomialEmbedding,
          realToComplexPlanePolynomial]


theorem projectiveCircularChart_planeHomogenizedLayer
    (c : ℂ) (D d : ℕ) (p : PlanePoly) :
    projectiveCircularChart c (planeHomogenizedLayer D d p) =
      circularChartZ ^ (D - d) *
        affineCircularChart c (MvPolynomial.homogeneousComponent d p) := by
  rw [planeHomogenizedLayer, map_mul, map_pow,
    projectiveCircularChart_realPlanePolynomialProjectiveEmbedding]
  simp [projectivePlaneZ, mul_comm]


theorem projectiveCircularChart_planeHomogenization
    (c : ℂ) (D : ℕ) (p : PlanePoly) :
    projectiveCircularChart c (planeHomogenization D p) =
      ∑ d ∈ Finset.range (D + 1),
        circularChartZ ^ (D - d) *
          affineCircularChart c (MvPolynomial.homogeneousComponent d p) := by
  simp only [planeHomogenization, map_sum, projectiveCircularChart_planeHomogenizedLayer]


end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace PachDeZeeuw.Algebraic

open MvPolynomial

 
theorem one_le_totalDegree_of_pderiv_ne_zero
    (p : PlanePoly) (i : Fin 2) (hpartial : pderiv i p ≠ 0) :
    1 ≤ p.totalDegree := by
  have hcoordinateDegree : MvPolynomial.degreeOf i p ≠ 0 := by
    intro hzero
    apply hpartial
    rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars]
    rw [MvPolynomial.mem_vars_iff_degreeOf_ne_zero]
    exact not_not_intro hzero
  rw [Nat.one_le_iff_ne_zero]
  intro htotalDegree
  apply hcoordinateDegree
  exact Nat.eq_zero_of_le_zero
    ((MvPolynomial.degreeOf_le_totalDegree p i).trans_eq htotalDegree)


end PachDeZeeuw.Algebraic
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open MvPolynomial
open PachDeZeeuw.Algebraic


theorem sharp_finite_common_zero_count
    (p q : PlanePoly) (S : Finset (Fin 2 → ℝ))
    (hirr : Irreducible p)
    (hpos : 1 ≤ p.totalDegree)
    (hnot : ¬ p ∣ q)
    (hzero : ∀ z ∈ S, MvPolynomial.eval z p = 0 ∧ MvPolynomial.eval z q = 0) :
    S.card ≤ p.totalDegree * q.totalDegree := by
  let toPoint : (Fin 2 → ℝ) → PachDeZeeuw.Algebraic.Point2 := fun z ↦ WithLp.toLp 2 z
  let P : Finset (ℝ × ℝ) := S.image (fun z ↦ chartEquiv (toPoint z))
  have hfamilyIrreducible :
      ∀ h ∈ ({p} : Finset PlanePoly), Irreducible h := by
    intro h hh
    rw [Finset.mem_singleton] at hh
    subst h
    exact hirr
  have hfamilyDegree :
      ∀ h ∈ ({p} : Finset PlanePoly), h.totalDegree ≤ p.totalDegree := by
    intro h hh
    rw [Finset.mem_singleton] at hh
    subst h
    exact le_rfl
  have hfamilyPositive :
      ∀ h ∈ ({p} : Finset PlanePoly), 1 ≤ h.totalDegree := by
    intro h hh
    rw [Finset.mem_singleton] at hh
    subst h
    exact hpos
  obtain ⟨s, hpderiv, hdegree, hirrShear, hseparate⟩ :=
    exists_good_shear ({p} : Finset PlanePoly) P p.totalDegree
      hfamilyIrreducible hfamilyDegree hfamilyPositive
  have hpmem : p ∈ ({p} : Finset PlanePoly) := Finset.mem_singleton_self p
  have hpderiv : pderiv (1 : Fin 2) (shearPoly s p) ≠ 0 := hpderiv p hpmem
  have hdegree : (shearPoly s p).totalDegree ≤ p.totalDegree := hdegree p hpmem
  have hirrShear : Irreducible (shearPoly s p) := hirrShear p hpmem
  let swap : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
  let p' : PlanePoly := MvPolynomial.rename swap (shearPoly s p)
  let q' : PlanePoly := MvPolynomial.rename swap (shearPoly s q)
  let phi : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun z ↦
    fun i ↦ swapPoint (chartEquiv.symm (shearPoint s (chartEquiv (toPoint z)))) i
  let T : Finset (Fin 2 → ℝ) := S.image phi
  have hphi : Set.InjOn phi (S : Set (Fin 2 → ℝ)) := by
    intro z hz w hw hzw
    have hswap :
        swapPoint (chartEquiv.symm (shearPoint s (chartEquiv (toPoint z)))) =
          swapPoint (chartEquiv.symm (shearPoint s (chartEquiv (toPoint w)))) := by
      ext i
      exact congrFun hzw i
    have hshear :
        chartEquiv.symm (shearPoint s (chartEquiv (toPoint z))) =
          chartEquiv.symm (shearPoint s (chartEquiv (toPoint w))) :=
      swapPoint_injective hswap
    have hfirst :
        (shearPoint s (chartEquiv (toPoint z))).1 =
          (shearPoint s (chartEquiv (toPoint w))).1 := by
      have hpair' := congrArg chartEquiv hshear
      exact congrArg Prod.fst hpair'
    have hzP : chartEquiv (toPoint z) ∈ P :=
      Finset.mem_image.mpr ⟨z, hz, rfl⟩
    have hwP : chartEquiv (toPoint w) ∈ P :=
      Finset.mem_image.mpr ⟨w, hw, rfl⟩
    have hpair : chartEquiv (toPoint z) = chartEquiv (toPoint w) :=
      hseparate hzP hwP hfirst
    have hpoint : toPoint z = toPoint w := chartEquiv.injective hpair
    funext i
    have hi := congrArg (fun x : PachDeZeeuw.Algebraic.Point2 ↦ x i) hpoint
    simpa [toPoint] using hi
  have hTcard : T.card = S.card := by
    exact Finset.card_image_iff.mpr hphi
  have hzero' :
      ∀ z ∈ T, MvPolynomial.eval z p' = 0 ∧ MvPolynomial.eval z q' = 0 := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    have hwp : MvPolynomial.eval w p = 0 := (hzero w hw).1
    have hwq : MvPolynomial.eval w q = 0 := (hzero w hw).2
    have hshearPoint := chartEquiv.symm (shearPoint s (chartEquiv (toPoint w)))
    constructor
    · rw [show p' = MvPolynomial.rename swap (shearPoly s p) by rfl]
      rw [eval_rename_swap_swapPoint]
      rw [eval_shearPoly_shearPoint_chart]
      simpa [toPoint] using hwp
    · rw [show q' = MvPolynomial.rename swap (shearPoly s q) by rfl]
      rw [eval_rename_swap_swapPoint]
      rw [eval_shearPoly_shearPoint_chart]
      simpa [toPoint] using hwq
  have hpartial' : pderiv (0 : Fin 2) p' ≠ 0 := by
    rw [show p' = MvPolynomial.rename swap (shearPoly s p) by rfl]
    have hrename :
        pderiv (0 : Fin 2) (MvPolynomial.rename swap (shearPoly s p)) =
          MvPolynomial.rename swap (pderiv (1 : Fin 2) (shearPoly s p)) := by
      simpa [swap] using
        (MvPolynomial.pderiv_rename swap.injective (x := (1 : Fin 2))
          (p := shearPoly s p))
    rw [hrename]
    exact (MvPolynomial.renameEquiv ℝ swap).injective.ne hpderiv
  have hpdegree' : 0 < (headCurry p').natDegree :=
    curry0_natDegree_pos_of_pderiv_zero_ne p' hpartial'
  have hirr' : Irreducible p' := by
    rw [show p' = MvPolynomial.rename swap (shearPoly s p) by rfl]
    exact hirrShear.map (MvPolynomial.renameEquiv ℝ swap).toRingEquiv
  have hnot' : ¬ p' ∣ q' := by
    intro hdiv
    change MvPolynomial.rename swap (shearPoly s p) ∣
      MvPolynomial.rename swap (shearPoly s q) at hdiv
    rw [← MvPolynomial.renameEquiv_apply, ← MvPolynomial.renameEquiv_apply] at hdiv
    have hdivShear : shearPoly s p ∣ shearPoly s q := by
      have hdiv' := map_dvd (MvPolynomial.renameEquiv ℝ swap).symm hdiv
      simpa only [AlgEquiv.symm_apply_apply] using hdiv'
    have hdivAlg : shearAlgEquiv s p ∣ shearAlgEquiv s q := by
      rw [shearAlgEquiv_apply, shearAlgEquiv_apply]
      exact hdivShear
    have hdivOrig := map_dvd (shearAlgEquiv s).symm hdivAlg
    exact hnot (by simpa only [AlgEquiv.symm_apply_apply] using hdivOrig)
  have hresultant : headResultant p' q' ≠ 0 :=
    headResultant_ne_zero_of_irreducible_not_dvd p' q' hpdegree' hirr' hnot'
  have hprojection : Set.InjOn (fun z : Fin 2 → ℝ ↦ z 1) (T : Set (Fin 2 → ℝ)) := by
    intro z hz w hw hzw
    obtain ⟨z₀, hz₀, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨w₀, hw₀, rfl⟩ := Finset.mem_image.mp hw
    have hi := hzw
    have hfirst :
        (shearPoint s (chartEquiv (toPoint z₀))).1 =
          (shearPoint s (chartEquiv (toPoint w₀))).1 := by
      simpa [phi, swapPoint, mkPoint2] using hi
    have hzP : chartEquiv (toPoint z₀) ∈ P :=
      Finset.mem_image.mpr ⟨z₀, hz₀, rfl⟩
    have hwP : chartEquiv (toPoint w₀) ∈ P :=
      Finset.mem_image.mpr ⟨w₀, hw₀, rfl⟩
    have hpair : chartEquiv (toPoint z₀) = chartEquiv (toPoint w₀) :=
      hseparate hzP hwP hfirst
    have hpoint : toPoint z₀ = toPoint w₀ := chartEquiv.injective hpair
    have hzw₀ : z₀ = w₀ := by
      funext i
      have hj := congrArg (fun x : PachDeZeeuw.Algebraic.Point2 ↦ x i) hpoint
      simpa [toPoint] using hj
    subst w₀
    rfl
  have hbound := common_zero_finset_card_le_totalDegree_mul
    p' q' T hpdegree' hresultant hprojection hzero'
  have hpdegreeBound : p'.totalDegree ≤ p.totalDegree := by
    dsimp [p']
    change ((MvPolynomial.renameEquiv ℝ swap) (shearPoly s p)).totalDegree ≤ p.totalDegree
    rw [MvPolynomial.totalDegree_renameEquiv]
    exact hdegree
  have hqdegreeBound : q'.totalDegree ≤ q.totalDegree := by
    dsimp [q']
    change ((MvPolynomial.renameEquiv ℝ swap) (shearPoly s q)).totalDegree ≤ q.totalDegree
    rw [MvPolynomial.totalDegree_renameEquiv]
    exact (shearPoly_totalDegree_le s q)
  calc
    S.card = T.card := hTcard.symm
    _ ≤ p'.totalDegree * q'.totalDegree := hbound
    _ ≤ p.totalDegree * q.totalDegree := Nat.mul_le_mul hpdegreeBound hqdegreeBound

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open EuclideanGeometry PachDeZeeuw


theorem preparedSecondCurvePolynomial_totalDegree_le {d : ℕ}
    (X : PreparedBipartiteInput d) :
    (preparedSecondCurvePolynomial X).totalDegree ≤ d :=
  (Classical.choose_spec X.hC₂).2.1


theorem preparedSecondCurvePolynomial_zeroSet {d : ℕ}
    (X : PreparedBipartiteInput d) :
    X.C₂ = PachDeZeeuw.Algebraic.PlaneCurveZeroSet
      (preparedSecondCurvePolynomial X) := by
  simpa [preparedSecondCurvePolynomial,
    PachDeZeeuw.Algebraic.PlaneCurveZeroSet] using
    (Classical.choose_spec X.hC₂).2.2.2


namespace AuxiliaryIncidenceDeletionCertificate


end AuxiliaryIncidenceDeletionCertificate


end Esgk

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

namespace IrreduciblePlanePolynomial


theorem exists_twoPairFunctionFieldAutomorphism_of_distanceImageIdeal_eq
    (C : IrreduciblePlanePolynomial ℝ)
    (g₁ g₂ : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) {r₁ r₂ : ℝ}
    (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0)
    (hns₁ :
      xAxisReflectionPoint ''
          PlaneCurveZeroSet (C.affineIsometryTransport g₁).polynomial ≠
        PlaneCurveZeroSet (C.affineIsometryTransport g₁).polynomial)
    (hns₂ :
      xAxisReflectionPoint ''
          PlaneCurveZeroSet (C.affineIsometryTransport g₂).polynomial ≠
        PlaneCurveZeroSet (C.affineIsometryTransport g₂).polynomial)
    (a c b d : PachDeZeeuw.Algebraic.Point2)
    (hg₁a : g₁ a = xAxisPoint (-r₁))
    (hg₁c : g₁ c = xAxisPoint r₁)
    (hg₂b : g₂ b = xAxisPoint (-r₂))
    (hg₂d : g₂ d = xAxisPoint r₂)
    (hIdeal :
      (C.affineIsometryTransport g₁).distanceImageIdeal r₁ =
        (C.affineIsometryTransport g₂).distanceImageIdeal r₂) :
    ∃ T : C.FunctionField ≃ₐ[ℝ] C.FunctionField,
      T (C.squaredDistanceFunctionAt b) = C.squaredDistanceFunctionAt a ∧
        T (C.squaredDistanceFunctionAt d) =
          C.squaredDistanceFunctionAt c := by
  have hcoords₁ :=
    C.normalizedDistanceImageFunctionFieldAlgEquiv_apply_coordinates
      g₁ hr₁ hns₁ a c hg₁a hg₁c
  have hcoords₂ :=
    C.normalizedDistanceImageFunctionFieldAlgEquiv_apply_coordinates
      g₂ hr₂ hns₂ b d hg₂b hg₂d
  obtain ⟨T, hTzero, hTone⟩ :=
    exists_commonImageFunctionFieldAutomorphism_of_sourceEquiv
      (C.normalizedDistanceImageFunctionFieldAlgEquiv g₁ hr₁ hns₁).toAlgHom
      (C.normalizedDistanceImageFunctionFieldAlgEquiv g₂ hr₂ hns₂).toAlgHom
      (distanceImageFunctionFieldAlgEquivOfIdealEq
        (C.affineIsometryTransport g₁)
        (C.affineIsometryTransport g₂) r₁ r₂ hIdeal)
      (C.normalizedDistanceImageFunctionFieldAlgEquiv g₁ hr₁ hns₁).surjective
      (C.normalizedDistanceImageFunctionFieldAlgEquiv g₂ hr₂ hns₂).surjective
      ((C.affineIsometryTransport g₁).distanceImageCoordinate r₁ 0)
      ((C.affineIsometryTransport g₁).distanceImageCoordinate r₁ 1)
  refine ⟨T, ?_, ?_⟩
  · rw [← hcoords₂.1, ← hcoords₁.1]
    simpa using hTzero
  · rw [← hcoords₂.2, ← hcoords₁.2]
    simpa using hTone

end IrreduciblePlanePolynomial

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic


private theorem inline_Esgk_PlaneCircularLocalOrderDegree__homogeneousComponent_totalDegree_ne_zero
    {G : PlanePoly} (hG : G ≠ 0) :
    MvPolynomial.homogeneousComponent G.totalDegree G ≠ 0 := by
  have hsupp : G.support.Nonempty := MvPolynomial.support_nonempty.mpr hG
  have hsup := Finset.sup_mem_of_nonempty
    (f := fun d : Fin 2 →₀ ℕ => d.sum fun _ e => e) hsupp
  rw [← MvPolynomial.totalDegree] at hsup
  rcases hsup with ⟨d, hd, hdegree⟩
  rw [← MvPolynomial.support_nonempty]
  refine ⟨d, ?_⟩
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_homogeneousComponent]
  have hdegree' : Finsupp.degree d = G.totalDegree := by
    simpa [Finsupp.degree_apply, Finsupp.sum] using hdegree
  simp only [hdegree', ↓reduceIte]
  exact MvPolynomial.mem_support_iff.mp hd

 
theorem realPlaneInfinityRestriction_ne_zero {G : PlanePoly} (hG : G ≠ 0) :
    realPlaneInfinityRestriction G ≠ 0 := by
  let q : MvPolynomial (Fin 2) ℝ :=
    (MvPolynomial.renameEquiv ℝ (Equiv.swap (0 : Fin 2) 1))
      (MvPolynomial.homogeneousComponent G.totalDegree G)
  have hqhom : q.IsHomogeneous G.totalDegree := by
    exact
      (MvPolynomial.homogeneousComponent_isHomogeneous G.totalDegree G).rename_isHomogeneous
  have hdehom : MvPolynomial.aeval ![Polynomial.X, 1] q =
      realPlaneInfinityRestriction G := by
    dsimp only [q]
    rw [MvPolynomial.renameEquiv_apply, MvPolynomial.aeval_rename]
    change (MvPolynomial.aeval (![(Polynomial.X : Polynomial ℝ), 1] ∘
        (Equiv.swap (0 : Fin 2) 1)))
        (MvPolynomial.homogeneousComponent G.totalDegree G) =
      (MvPolynomial.aeval ![(1 : Polynomial ℝ), Polynomial.X])
        (MvPolynomial.homogeneousComponent G.totalDegree G)
    have hvec : (![(Polynomial.X : Polynomial ℝ), 1] ∘
        (Equiv.swap (0 : Fin 2) 1)) = ![(1 : Polynomial ℝ), Polynomial.X] := by
      funext i
      fin_cases i <;> simp
    rw [hvec]
  intro hzero
  have hqzero : q = 0 := by
    rw [← Polynomial.homogenize_eq_of_isHomogeneous hqhom hdehom, hzero]
    simp
  apply inline_Esgk_PlaneCircularLocalOrderDegree__homogeneousComponent_totalDegree_ne_zero hG
  exact (MvPolynomial.renameEquiv ℝ (Equiv.swap (0 : Fin 2) 1)).injective
    (by simpa only [map_zero] using hqzero)

 
theorem complexPlaneInfinityRestriction_ne_zero {G : PlanePoly} (hG : G ≠ 0) :
    complexPlaneInfinityRestriction G ≠ 0 := by
  exact (Polynomial.map_ne_zero_iff Complex.ofReal_injective).mpr
    (realPlaneInfinityRestriction_ne_zero hG)

 
theorem realPlaneInfinityRestriction_natDegree_le (G : PlanePoly) :
    (realPlaneInfinityRestriction G).natDegree ≤ G.totalDegree := by
  change (MvPolynomial.aeval ![(1 : Polynomial ℝ), Polynomial.X]
    (MvPolynomial.homogeneousComponent G.totalDegree G)).natDegree ≤ G.totalDegree
  simpa using MvPolynomial.aeval_natDegree_le
    (m := G.totalDegree) (n := 1)
    (MvPolynomial.homogeneousComponent G.totalDegree G)
    (MvPolynomial.homogeneousComponent_isHomogeneous G.totalDegree G).totalDegree_le
    ![(1 : Polynomial ℝ), Polynomial.X]
    (fun i ↦ by fin_cases i <;> simp)

 
theorem complexPlaneInfinityRestriction_natDegree_le (G : PlanePoly) :
    (complexPlaneInfinityRestriction G).natDegree ≤ G.totalDegree :=
  Polynomial.natDegree_map_le.trans (realPlaneInfinityRestriction_natDegree_le G)


theorem projectiveInfinityRestriction_realPlanePolynomialProjectiveEmbedding (p : PlanePoly) :
    projectiveInfinityRestriction (realPlanePolynomialProjectiveEmbedding p) =
      (realPlaneOneXRestriction p).map Complex.ofRealHom := by
  induction p using MvPolynomial.induction_on with
  | C r =>
      simp [projectiveInfinityRestriction, realPlanePolynomialProjectiveEmbedding,
        complexPlanePolynomialEmbedding, realToComplexPlanePolynomial,
        realPlaneOneXRestriction]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, hp]
      fin_cases i <;>
        simp [projectiveInfinityRestriction, realPlanePolynomialProjectiveEmbedding,
          complexPlanePolynomialEmbedding, realToComplexPlanePolynomial,
          realPlaneOneXRestriction]


theorem projectiveInfinityRestriction_planeHomogenization (D : ℕ) (G : PlanePoly) :
    projectiveInfinityRestriction (planeHomogenization D G) =
      (realPlaneOneXRestriction (MvPolynomial.homogeneousComponent D G)).map
        Complex.ofRealHom := by
  rw [planeHomogenization, map_sum, Finset.sum_eq_single D]
  · simp [planeHomogenizedLayer,
      projectiveInfinityRestriction_realPlanePolynomialProjectiveEmbedding]
  · intro d hd hdD
    have hdle : d ≤ D := by
      simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hd
    have hdlt : d < D := lt_of_le_of_ne hdle hdD
    have hpow : D - d ≠ 0 := Nat.sub_ne_zero_of_lt hdlt
    simp [planeHomogenizedLayer, projectiveInfinityRestriction, projectivePlaneZ, hpow]
  · simp

 
theorem projectiveInfinityRestriction_planeHomogenization_totalDegree (G : PlanePoly) :
    projectiveInfinityRestriction (planeHomogenization G.totalDegree G) =
      complexPlaneInfinityRestriction G := by
  exact projectiveInfinityRestriction_planeHomogenization G.totalDegree G


theorem chartInfinityRestriction_coeff (p : CircularChartPoly) (n : ℕ) :
    (chartInfinityRestriction p).coeff n =
      MvPolynomial.coeff (Finsupp.cons n (0 : Fin 1 →₀ ℕ)) p := by
  change (Polynomial.map
    (MvPolynomial.constantCoeff : MvPolynomial (Fin 1) ℂ →+* ℂ)
    ((MvPolynomial.finSuccEquiv ℂ 1) p)).coeff n =
      MvPolynomial.coeff (Finsupp.cons n (0 : Fin 1 →₀ ℕ)) p
  rw [Polynomial.coeff_map]
  change MvPolynomial.coeff 0 (((MvPolynomial.finSuccEquiv ℂ 1) p).coeff n) =
    MvPolynomial.coeff (Finsupp.cons n (0 : Fin 1 →₀ ℕ)) p
  exact MvPolynomial.finSuccEquiv_coeff_coeff 0 p n

@[simp]
theorem chartInfinityRestriction_C (c : ℂ) :
    chartInfinityRestriction (MvPolynomial.C c) = Polynomial.C c := by
  change Polynomial.map
      (MvPolynomial.constantCoeff : MvPolynomial (Fin 1) ℂ →+* ℂ)
      ((MvPolynomial.finSuccEquiv ℂ 1) (MvPolynomial.C c)) = Polynomial.C c
  rw [MvPolynomial.finSuccEquiv_apply]
  simp

@[simp]
theorem chartInfinityRestriction_circularChartU :
    chartInfinityRestriction circularChartU = Polynomial.X := by
  change Polynomial.map
      (MvPolynomial.constantCoeff : MvPolynomial (Fin 1) ℂ →+* ℂ)
      ((MvPolynomial.finSuccEquiv ℂ 1) (MvPolynomial.X 0)) = Polynomial.X
  rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X]

@[simp]
theorem chartInfinityRestriction_circularChartZ :
    chartInfinityRestriction circularChartZ = 0 := by
  change Polynomial.map
      (MvPolynomial.constantCoeff : MvPolynomial (Fin 1) ℂ →+* ℂ)
      ((MvPolynomial.finSuccEquiv ℂ 1) (MvPolynomial.X 1)) = 0
  rw [show (1 : Fin 2) = (0 : Fin 1).succ by rfl, MvPolynomial.finSuccEquiv_X_succ]
  simp


theorem chartInfinityRestriction_projectiveCircularChart
    (c : ℂ) (P : ProjectivePlanePoly) :
    chartInfinityRestriction (projectiveCircularChart c P) =
      (projectiveInfinityRestriction P).comp (Polynomial.X + Polynomial.C c) := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [projectiveCircularChart, projectiveInfinityRestriction]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, hp]
      fin_cases i <;>
        simp [projectiveCircularChart, projectiveInfinityRestriction, add_comm]


theorem chartInfinityRestriction_projectiveCircularChart_planeHomogenization
    (c : ℂ) (G : PlanePoly) :
    chartInfinityRestriction
        (projectiveCircularChart c (planeHomogenization G.totalDegree G)) =
      (complexPlaneInfinityRestriction G).comp (Polynomial.X + Polynomial.C c) := by
  rw [chartInfinityRestriction_projectiveCircularChart,
    projectiveInfinityRestriction_planeHomogenization_totalDegree]


private theorem inline_Esgk_PlaneCircularLocalOrderDegree__localOrder_toNat_le_rootMultiplicity_of_chartInfinityRestriction_eq
    (c : ℂ) (F : CircularChartPoly) (p : Polynomial ℂ) (hp : p ≠ 0)
    (hrestrict :
      chartInfinityRestriction F = p.comp (Polynomial.X + Polynomial.C c)) :
    (MvPolynomial.localOrder F).toNat ≤ p.rootMultiplicity c := by
  let q := p.comp (Polynomial.X + Polynomial.C c)
  have hq : q ≠ 0 := Polynomial.comp_X_add_C_ne_zero_iff.mpr hp
  have hcoeffq : q.coeff q.natTrailingDegree ≠ 0 :=
    Polynomial.coeff_natTrailingDegree_ne_zero.mpr hq
  have hcoeff :
      MvPolynomial.coeff
        (Finsupp.cons q.natTrailingDegree (0 : Fin 1 →₀ ℕ)) F ≠ 0 := by
    rw [← chartInfinityRestriction_coeff, hrestrict]
    exact hcoeffq
  have hcoeffSeries :
      MvPowerSeries.coeff
        (Finsupp.cons q.natTrailingDegree (0 : Fin 1 →₀ ℕ))
        (F : MvPowerSeries (Fin 2) ℂ) ≠ 0 := by
    simpa using hcoeff
  have hdegree :
      Finsupp.degree (Finsupp.cons q.natTrailingDegree (0 : Fin 1 →₀ ℕ)) =
        q.natTrailingDegree := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two, Finsupp.cons_zero]
    change q.natTrailingDegree +
      (Finsupp.cons q.natTrailingDegree (0 : Fin 1 →₀ ℕ)) (0 : Fin 1).succ =
        q.natTrailingDegree
    rw [Finsupp.cons_succ]
    simp
  have horder : MvPolynomial.localOrder F ≤ (q.natTrailingDegree : ℕ∞) := by
    simpa [MvPolynomial.localOrder, hdegree] using
      (MvPowerSeries.order_le hcoeffSeries)
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree]
  exact ENat.toNat_le_of_le_coe horder


theorem planeCircularLocalOrder_le_rootMultiplicity
    (c : ℂ) {G : PlanePoly} (hG : G ≠ 0) :
    planeCircularLocalOrder c G ≤
      (complexPlaneInfinityRestriction G).rootMultiplicity c := by
  exact inline_Esgk_PlaneCircularLocalOrderDegree__localOrder_toNat_le_rootMultiplicity_of_chartInfinityRestriction_eq
    c (projectiveCircularChart c (planeHomogenization G.totalDegree G))
    (complexPlaneInfinityRestriction G) (complexPlaneInfinityRestriction_ne_zero hG)
    (chartInfinityRestriction_projectiveCircularChart_planeHomogenization c G)


private theorem inline_Esgk_PlaneCircularLocalOrderDegree__multiset_count_add_count_le_card_of_ne
    {R : Type*} [DecidableEq R] {a b : R} (hab : a ≠ b) (s : Multiset R) :
    s.count a + s.count b ≤ s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons x s ih =>
      by_cases hxa : x = a
      · subst x
        simp only [Multiset.card_cons, Multiset.count_cons, if_neg (Ne.symm hab), add_zero,
          if_true]
        omega
      · by_cases hxb : x = b
        · subst x
          simp only [Multiset.card_cons, Multiset.count_cons, if_neg hab, add_zero, if_true]
          omega
        · have hax : a ≠ x := Ne.symm hxa
          have hbx : b ≠ x := Ne.symm hxb
          simp only [Multiset.card_cons, Multiset.count_cons, if_neg hax,
            if_neg hbx, add_zero]
          omega

 
theorem Polynomial.rootMultiplicity_add_rootMultiplicity_le_natDegree_of_ne
    {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]
    (p : Polynomial R) {a b : R} (hab : a ≠ b) :
    p.rootMultiplicity a + p.rootMultiplicity b ≤ p.natDegree := by
  rw [← Polynomial.count_roots p, ← Polynomial.count_roots p]
  exact (inline_Esgk_PlaneCircularLocalOrderDegree__multiset_count_add_count_le_card_of_ne hab p.roots).trans
    (Polynomial.card_roots' p)


end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

namespace IrreduciblePlanePolynomial


theorem eval_normalizedDistancePairPolynomialHom
    (r : ℝ) (p : MvPolynomial (Fin 2) ℝ) (x : PachDeZeeuw.Algebraic.Point2) :
    MvPolynomial.eval (fun i ↦ x i)
        (normalizedDistancePairPolynomialHom r p) =
      MvPolynomial.eval (normalizedDistanceOutputValue r x) p := by
  change
    MvPolynomial.eval₂Hom (RingHom.id ℝ) (fun i ↦ x i)
        (MvPolynomial.bind₁
          ![normalizedLeftSquaredDistancePolynomial r,
            normalizedRightSquaredDistancePolynomial r] p) =
      MvPolynomial.eval₂Hom (RingHom.id ℝ)
        (normalizedDistanceOutputValue r x) p
  rw [MvPolynomial.eval₂Hom_bind₁]
  refine MvPolynomial.eval₂Hom_congr rfl ?_ rfl
  funext i
  fin_cases i <;>
    simp [normalizedDistanceOutputValue,
      normalizedLeftSquaredDistancePolynomial,
      normalizedRightSquaredDistancePolynomial, normalizedLeftValue,
      normalizedRightValue]


theorem distancePairAlgHom_apply_eq_mk_normalizedDistancePairPolynomialHom
    (C : IrreduciblePlanePolynomial ℝ) (r : ℝ)
    (p : MvPolynomial (Fin 2) ℝ) :
    C.distancePairAlgHom r p =
      Ideal.Quotient.mk
        (Ideal.span ({C.polynomial} : Set (MvPolynomial (Fin 2) ℝ)))
        (normalizedDistancePairPolynomialHom r p) := by
  let q := Ideal.Quotient.mkₐ ℝ
    (Ideal.span ({C.polynomial} : Set (MvPolynomial (Fin 2) ℝ)))
  have hhom : C.distancePairAlgHom r =
      q.comp (normalizedDistancePairPolynomialHom r) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simpa [q, normalizedDistancePairPolynomialHom] using
        (mk_normalizedLeftSquaredDistancePolynomial C r).symm
    · simpa [q, normalizedDistancePairPolynomialHom] using
        (mk_normalizedRightSquaredDistancePolynomial C r).symm
  exact DFunLike.congr_fun hhom p


theorem mem_distanceImageIdeal_iff_dvd_normalizedDistancePairPolynomialHom
    (C : IrreduciblePlanePolynomial ℝ) (r : ℝ)
    (p : MvPolynomial (Fin 2) ℝ) :
    p ∈ C.distanceImageIdeal r ↔
      C.polynomial ∣ normalizedDistancePairPolynomialHom r p := by
  change C.distancePairAlgHom r p = 0 ↔ _
  rw [distancePairAlgHom_apply_eq_mk_normalizedDistancePairPolynomialHom,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]


theorem normalizedLeftValue_eq_dist_xAxisPoint_neg
    (r : ℝ) (x : PachDeZeeuw.Algebraic.Point2) :
    normalizedLeftValue r x = dist x (xAxisPoint (-r)) ^ 2 := by
  rw [← eval_planeSquaredDistancePolynomial]
  simp [normalizedLeftValue]


theorem normalizedRightValue_eq_dist_xAxisPoint
    (r : ℝ) (x : PachDeZeeuw.Algebraic.Point2) :
    normalizedRightValue r x = dist x (xAxisPoint r) ^ 2 := by
  rw [← eval_planeSquaredDistancePolynomial]
  simp [normalizedRightValue]


theorem pairAffineIsometry_image_twoPairDistanceCommonZeroSet_subset
    (C : IrreduciblePlanePolynomial ℝ)
    (g₁ g₂ : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) {r₁ r₂ : ℝ}
    (a c b d : PachDeZeeuw.Algebraic.Point2)
    (hg₁a : g₁ a = xAxisPoint (-r₁))
    (hg₁c : g₁ c = xAxisPoint r₁)
    (hg₂b : g₂ b = xAxisPoint (-r₂))
    (hg₂d : g₂ d = xAxisPoint r₂) :
    (fun z : PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2 ↦ (g₁ z.1, g₂ z.2)) ''
        twoPairDistanceCommonZeroSet C a c b d ⊆
      normalizedDistancePairCommonZeroSet
        (C.affineIsometryTransport g₁)
        (C.affineIsometryTransport g₂) r₁ r₂ := by
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← C.affineIsometry_image_zeroSet_eq g₁]
    exact ⟨z.1, hz.1, rfl⟩
  · rw [← C.affineIsometry_image_zeroSet_eq g₂]
    exact ⟨z.2, hz.2.1, rfl⟩
  · rw [normalizedLeftValue_eq_dist_xAxisPoint_neg,
      normalizedLeftValue_eq_dist_xAxisPoint_neg, ← hg₁a, ← hg₂b,
      g₁.dist_map, g₂.dist_map]
    exact hz.2.2.1
  · rw [normalizedRightValue_eq_dist_xAxisPoint,
      normalizedRightValue_eq_dist_xAxisPoint, ← hg₁c, ← hg₂d,
      g₁.dist_map, g₂.dist_map]
    exact hz.2.2.2


theorem normalizedDistancePairCommonZeroSet_infinite_of_twoPair
    (C : IrreduciblePlanePolynomial ℝ)
    (g₁ g₂ : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) {r₁ r₂ : ℝ}
    (a c b d : PachDeZeeuw.Algebraic.Point2)
    (hg₁a : g₁ a = xAxisPoint (-r₁))
    (hg₁c : g₁ c = xAxisPoint r₁)
    (hg₂b : g₂ b = xAxisPoint (-r₂))
    (hg₂d : g₂ d = xAxisPoint r₂)
    (hinf : (twoPairDistanceCommonZeroSet C a c b d).Infinite) :
    (normalizedDistancePairCommonZeroSet
      (C.affineIsometryTransport g₁)
      (C.affineIsometryTransport g₂) r₁ r₂).Infinite := by
  have hinjective : Function.Injective
      (fun z : PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2 ↦ (g₁ z.1, g₂ z.2)) := by
    intro z w hzw
    apply Prod.ext
    · exact g₁.injective (congrArg Prod.fst hzw)
    · exact g₂.injective (congrArg Prod.snd hzw)
  have himage :
      ((fun z : PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2 ↦ (g₁ z.1, g₂ z.2)) ''
        twoPairDistanceCommonZeroSet C a c b d).Infinite :=
    hinf.image hinjective.injOn
  exact himage.mono
    (pairAffineIsometry_image_twoPairDistanceCommonZeroSet_subset
      C g₁ g₂ a c b d hg₁a hg₁c hg₂b hg₂d)


theorem distanceImageIdeal_eq_of_infinite_normalized_correspondence
    (C₁ C₂ : IrreduciblePlanePolynomial ℝ) (r₁ r₂ : ℝ)
    (U : Set (PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2))
    (hfirst : (Prod.fst '' U).Infinite)
    (hsecond : (Prod.snd '' U).Infinite)
    (hC₁ : ∀ z ∈ U, z.1 ∈ PlaneCurveZeroSet C₁.polynomial)
    (hC₂ : ∀ z ∈ U, z.2 ∈ PlaneCurveZeroSet C₂.polynomial)
    (hleft : ∀ z ∈ U,
      normalizedLeftValue r₁ z.1 = normalizedLeftValue r₂ z.2)
    (hright : ∀ z ∈ U,
      normalizedRightValue r₁ z.1 = normalizedRightValue r₂ z.2) :
    C₁.distanceImageIdeal r₁ = C₂.distanceImageIdeal r₂ := by
  ext p
  constructor
  · intro hp
    let q₁ := normalizedDistancePairPolynomialHom r₁ p
    let q₂ := normalizedDistancePairPolynomialHom r₂ p
    have hdiv₁ : C₁.polynomial ∣ q₁ :=
      (mem_distanceImageIdeal_iff_dvd_normalizedDistancePairPolynomialHom
        C₁ r₁ p).mp hp
    have hsubset : Prod.snd '' U ⊆
        PlaneCurveZeroSet C₂.polynomial ∩ PlaneCurveZeroSet q₂ := by
      rintro y ⟨z, hz, rfl⟩
      refine ⟨hC₂ z hz, ?_⟩
      have hq₁ : z.1 ∈ PlaneCurveZeroSet q₁ :=
        PlaneCurveZeroSet_subset_of_dvd hdiv₁ (hC₁ z hz)
      have hout : normalizedDistanceOutputValue r₁ z.1 =
          normalizedDistanceOutputValue r₂ z.2 := by
        funext i
        fin_cases i
        · exact hleft z hz
        · exact hright z hz
      rw [mem_PlaneCurveZeroSet] at hq₁ ⊢
      calc
        MvPolynomial.eval (fun i ↦ z.2 i) q₂ =
            MvPolynomial.eval (normalizedDistanceOutputValue r₂ z.2) p :=
          eval_normalizedDistancePairPolynomialHom r₂ p z.2
        _ = MvPolynomial.eval (normalizedDistanceOutputValue r₁ z.1) p :=
          congrArg (fun f ↦ MvPolynomial.eval f p) hout.symm
        _ = MvPolynomial.eval (fun i ↦ z.1 i) q₁ :=
          (eval_normalizedDistancePairPolynomialHom r₁ p z.1).symm
        _ = 0 := hq₁
    have hinf :
        (PlaneCurveZeroSet C₂.polynomial ∩ PlaneCurveZeroSet q₂).Infinite :=
      hsecond.mono hsubset
    have hdiv₂ : C₂.polynomial ∣ q₂ :=
      dvd_of_infinite_irreducible_zeroSet_intersection C₂.irreducible hinf
    exact
      (mem_distanceImageIdeal_iff_dvd_normalizedDistancePairPolynomialHom
        C₂ r₂ p).mpr hdiv₂
  · intro hp
    let q₁ := normalizedDistancePairPolynomialHom r₁ p
    let q₂ := normalizedDistancePairPolynomialHom r₂ p
    have hdiv₂ : C₂.polynomial ∣ q₂ :=
      (mem_distanceImageIdeal_iff_dvd_normalizedDistancePairPolynomialHom
        C₂ r₂ p).mp hp
    have hsubset : Prod.fst '' U ⊆
        PlaneCurveZeroSet C₁.polynomial ∩ PlaneCurveZeroSet q₁ := by
      rintro x ⟨z, hz, rfl⟩
      refine ⟨hC₁ z hz, ?_⟩
      have hq₂ : z.2 ∈ PlaneCurveZeroSet q₂ :=
        PlaneCurveZeroSet_subset_of_dvd hdiv₂ (hC₂ z hz)
      have hout : normalizedDistanceOutputValue r₁ z.1 =
          normalizedDistanceOutputValue r₂ z.2 := by
        funext i
        fin_cases i
        · exact hleft z hz
        · exact hright z hz
      rw [mem_PlaneCurveZeroSet] at hq₂ ⊢
      calc
        MvPolynomial.eval (fun i ↦ z.1 i) q₁ =
            MvPolynomial.eval (normalizedDistanceOutputValue r₁ z.1) p :=
          eval_normalizedDistancePairPolynomialHom r₁ p z.1
        _ = MvPolynomial.eval (normalizedDistanceOutputValue r₂ z.2) p :=
          congrArg (fun f ↦ MvPolynomial.eval f p) hout
        _ = MvPolynomial.eval (fun i ↦ z.2 i) q₂ :=
          (eval_normalizedDistancePairPolynomialHom r₂ p z.2).symm
        _ = 0 := hq₂
    have hinf :
        (PlaneCurveZeroSet C₁.polynomial ∩ PlaneCurveZeroSet q₁).Infinite :=
      hfirst.mono hsubset
    have hdiv₁ : C₁.polynomial ∣ q₁ :=
      dvd_of_infinite_irreducible_zeroSet_intersection C₁.irreducible hinf
    exact
      (mem_distanceImageIdeal_iff_dvd_normalizedDistancePairPolynomialHom
        C₁ r₁ p).mpr hdiv₁


theorem distanceImageIdeal_eq_of_infinite_commonZeroSet
    (C₁ C₂ : IrreduciblePlanePolynomial ℝ) {r₁ r₂ : ℝ}
    (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0)
    (hinf : (normalizedDistancePairCommonZeroSet C₁ C₂ r₁ r₂).Infinite) :
    C₁.distanceImageIdeal r₁ = C₂.distanceImageIdeal r₂ := by
  let U := normalizedDistancePairCommonZeroSet C₁ C₂ r₁ r₂
  have hleft : ∀ z ∈ U,
      normalizedLeftValue r₁ z.1 = normalizedLeftValue r₂ z.2 :=
    fun z hz ↦ hz.2.2.1
  have hright : ∀ z ∈ U,
      normalizedRightValue r₁ z.1 = normalizedRightValue r₂ z.2 :=
    fun z hz ↦ hz.2.2.2
  exact distanceImageIdeal_eq_of_infinite_normalized_correspondence
    C₁ C₂ r₁ r₂ U
    (normalized_projection_fst_infinite hinf hr₂ hleft hright)
    (normalized_projection_snd_infinite hinf hr₁ hleft hright)
    (fun z hz ↦ hz.1) (fun z hz ↦ hz.2.1) hleft hright


theorem exists_twoPairFunctionFieldAutomorphism_of_infinite_commonZeroSet
    (C : IrreduciblePlanePolynomial ℝ)
    (g₁ g₂ : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) {r₁ r₂ : ℝ}
    (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0)
    (hns₁ :
      xAxisReflectionPoint ''
          PlaneCurveZeroSet (C.affineIsometryTransport g₁).polynomial ≠
        PlaneCurveZeroSet (C.affineIsometryTransport g₁).polynomial)
    (hns₂ :
      xAxisReflectionPoint ''
          PlaneCurveZeroSet (C.affineIsometryTransport g₂).polynomial ≠
        PlaneCurveZeroSet (C.affineIsometryTransport g₂).polynomial)
    (a c b d : PachDeZeeuw.Algebraic.Point2)
    (hg₁a : g₁ a = xAxisPoint (-r₁))
    (hg₁c : g₁ c = xAxisPoint r₁)
    (hg₂b : g₂ b = xAxisPoint (-r₂))
    (hg₂d : g₂ d = xAxisPoint r₂)
    (hinf :
      (normalizedDistancePairCommonZeroSet
        (C.affineIsometryTransport g₁)
        (C.affineIsometryTransport g₂) r₁ r₂).Infinite) :
    ∃ T : C.FunctionField ≃ₐ[ℝ] C.FunctionField,
      T (C.squaredDistanceFunctionAt b) = C.squaredDistanceFunctionAt a ∧
        T (C.squaredDistanceFunctionAt d) =
          C.squaredDistanceFunctionAt c := by
  apply exists_twoPairFunctionFieldAutomorphism_of_distanceImageIdeal_eq
    C g₁ g₂ hr₁ hr₂ hns₁ hns₂ a c b d hg₁a hg₁c hg₂b hg₂d
  exact distanceImageIdeal_eq_of_infinite_commonZeroSet
    (C.affineIsometryTransport g₁) (C.affineIsometryTransport g₂)
    hr₁ hr₂ hinf


theorem exists_twoPairFunctionFieldAutomorphism_of_infinite_intersection
    (C : IrreduciblePlanePolynomial ℝ)
    (g₁ g₂ : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) {r₁ r₂ : ℝ}
    (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0)
    (hns₁ :
      xAxisReflectionPoint ''
          PlaneCurveZeroSet (C.affineIsometryTransport g₁).polynomial ≠
        PlaneCurveZeroSet (C.affineIsometryTransport g₁).polynomial)
    (hns₂ :
      xAxisReflectionPoint ''
          PlaneCurveZeroSet (C.affineIsometryTransport g₂).polynomial ≠
        PlaneCurveZeroSet (C.affineIsometryTransport g₂).polynomial)
    (a c b d : PachDeZeeuw.Algebraic.Point2)
    (hg₁a : g₁ a = xAxisPoint (-r₁))
    (hg₁c : g₁ c = xAxisPoint r₁)
    (hg₂b : g₂ b = xAxisPoint (-r₂))
    (hg₂d : g₂ d = xAxisPoint r₂)
    (hinf : (twoPairDistanceCommonZeroSet C a c b d).Infinite) :
    ∃ T : C.FunctionField ≃ₐ[ℝ] C.FunctionField,
      T (C.squaredDistanceFunctionAt b) = C.squaredDistanceFunctionAt a ∧
        T (C.squaredDistanceFunctionAt d) =
          C.squaredDistanceFunctionAt c := by
  apply exists_twoPairFunctionFieldAutomorphism_of_infinite_commonZeroSet
    C g₁ g₂ hr₁ hr₂ hns₁ hns₂ a c b d hg₁a hg₁c hg₂b hg₂d
  exact normalizedDistancePairCommonZeroSet_infinite_of_twoPair
    C g₁ g₂ a c b d hg₁a hg₁c hg₂b hg₂d hinf

end IrreduciblePlanePolynomial

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace MvPolynomial

 
theorem localOrder_map_star {σ : Type*} (p : MvPolynomial σ ℂ) :
    localOrder (map (starRingEnd ℂ) p) = localOrder p := by
  have hcoe :
      ((map (starRingEnd ℂ) p : MvPolynomial σ ℂ) : MvPowerSeries σ ℂ) =
        MvPowerSeries.map (starRingEnd ℂ) (p : MvPowerSeries σ ℂ) := by
    ext d
    exact MvPolynomial.coeff_map (starRingEnd ℂ) p d
  rw [localOrder, localOrder, hcoe]
  apply le_antisymm
  · have h := MvPowerSeries.le_order_map (starRingEnd ℂ)
      (φ := MvPowerSeries.map (starRingEnd ℂ) (p : MvPowerSeries σ ℂ))
    have hinvolution :
        MvPowerSeries.map (starRingEnd ℂ)
            (MvPowerSeries.map (starRingEnd ℂ) (p : MvPowerSeries σ ℂ)) = p := by
      ext d
      simp
    rw [hinvolution] at h
    exact h
  · exact MvPowerSeries.le_order_map (starRingEnd ℂ)

end MvPolynomial

namespace Esgk

open PachDeZeeuw.Algebraic

private theorem inline_Esgk_PlaneCircularLocalOrderConjugation__realPlanePolynomialProjectiveEmbedding_map_star (p : PlanePoly) :
    MvPolynomial.map (starRingEnd ℂ) (realPlanePolynomialProjectiveEmbedding p) =
      realPlanePolynomialProjectiveEmbedding p := by
  change
    MvPolynomial.map (starRingEnd ℂ)
        (MvPolynomial.rename Fin.castSucc (MvPolynomial.map Complex.ofRealHom p)) =
      MvPolynomial.rename Fin.castSucc (MvPolynomial.map Complex.ofRealHom p)
  rw [MvPolynomial.map_rename, MvPolynomial.map_map]
  have hcomp : (starRingEnd ℂ).comp Complex.ofRealHom = Complex.ofRealHom := by
    ext r
    simp
  rw [hcomp]

private theorem inline_Esgk_PlaneCircularLocalOrderConjugation__planeHomogenization_map_star (D : ℕ) (G : PlanePoly) :
    MvPolynomial.map (starRingEnd ℂ) (planeHomogenization D G) = planeHomogenization D G := by
  simp only [planeHomogenization, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp [planeHomogenizedLayer, inline_Esgk_PlaneCircularLocalOrderConjugation__realPlanePolynomialProjectiveEmbedding_map_star,
    projectivePlaneZ]

private theorem inline_Esgk_PlaneCircularLocalOrderConjugation__projectiveCircularChart_map_star (c : ℂ) (P : ProjectivePlanePoly) :
    MvPolynomial.map (starRingEnd ℂ) (projectiveCircularChart c P) =
      projectiveCircularChart ((starRingEnd ℂ) c)
        (MvPolynomial.map (starRingEnd ℂ) P) := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [projectiveCircularChart]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, hp]
      fin_cases i <;>
        simp [projectiveCircularChart, circularChartU, circularChartZ]


theorem projectiveCircularChart_planeHomogenization_map_star (c : ℂ) (G : PlanePoly) :
    MvPolynomial.map (starRingEnd ℂ)
        (projectiveCircularChart c (planeHomogenization G.totalDegree G)) =
      projectiveCircularChart ((starRingEnd ℂ) c)
        (planeHomogenization G.totalDegree G) := by
  rw [inline_Esgk_PlaneCircularLocalOrderConjugation__projectiveCircularChart_map_star, inline_Esgk_PlaneCircularLocalOrderConjugation__planeHomogenization_map_star]

 
theorem projectiveCircularChartI_planeHomogenization_map_star (G : PlanePoly) :
    MvPolynomial.map (starRingEnd ℂ)
        (projectiveCircularChartI (planeHomogenization G.totalDegree G)) =
      projectiveCircularChartJ (planeHomogenization G.totalDegree G) := by
  simpa [projectiveCircularChartI, projectiveCircularChartJ, Complex.conj_I] using
    projectiveCircularChart_planeHomogenization_map_star Complex.I G


theorem planeCircularLocalOrderI_eq_planeCircularLocalOrderJ (G : PlanePoly) :
    planeCircularLocalOrderI G = planeCircularLocalOrderJ G := by
  change
    (MvPolynomial.localOrder
        (projectiveCircularChartI (planeHomogenization G.totalDegree G))).toNat =
      (MvPolynomial.localOrder
        (projectiveCircularChartJ (planeHomogenization G.totalDegree G))).toNat
  have h := MvPolynomial.localOrder_map_star
    (projectiveCircularChartI (planeHomogenization G.totalDegree G))
  rw [projectiveCircularChartI_planeHomogenization_map_star] at h
  exact congrArg ENat.toNat h.symm

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic


theorem IsMaximallyCircular.order_sum_eq_totalDegree
    {G : PlanePoly} (hG : IsMaximallyCircular G) :
    planeCircularLocalOrderI G + planeCircularLocalOrderJ G = G.totalDegree := by
  rcases hG with ⟨hI, hJ⟩
  omega


variable {n : ℕ}


end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

namespace IrreduciblePlanePolynomial


theorem exists_affineNormalizationRingAlgEquiv_of_infinite_intersection
    (C : IrreduciblePlanePolynomial ℝ)
    (g₁ g₂ : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) {r₁ r₂ : ℝ}
    (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0)
    (hns₁ :
      xAxisReflectionPoint ''
          PlaneCurveZeroSet (C.affineIsometryTransport g₁).polynomial ≠
        PlaneCurveZeroSet (C.affineIsometryTransport g₁).polynomial)
    (hns₂ :
      xAxisReflectionPoint ''
          PlaneCurveZeroSet (C.affineIsometryTransport g₂).polynomial ≠
        PlaneCurveZeroSet (C.affineIsometryTransport g₂).polynomial)
    (a c b d : PachDeZeeuw.Algebraic.Point2)
    (hg₁a : g₁ a = xAxisPoint (-r₁))
    (hg₁c : g₁ c = xAxisPoint r₁)
    (hg₂b : g₂ b = xAxisPoint (-r₂))
    (hg₂d : g₂ d = xAxisPoint r₂)
    (hinf : (twoPairDistanceCommonZeroSet C a c b d).Infinite) :
    ∃ degreeRight : C.affineNormalizationRing ≃ₐ[ℝ] C.affineNormalizationRing,
      degreeRight (C.affineNormalizationLift (C.squaredDistanceClassAt b)) =
          C.affineNormalizationLift (C.squaredDistanceClassAt a) ∧
        degreeRight (C.affineNormalizationLift (C.squaredDistanceClassAt d)) =
          C.affineNormalizationLift (C.squaredDistanceClassAt c) := by
  obtain ⟨T, hTb, hTd⟩ :=
    C.exists_twoPairFunctionFieldAutomorphism_of_infinite_intersection
      g₁ g₂ hr₁ hr₂ hns₁ hns₂ a c b d hg₁a hg₁c hg₂b hg₂d hinf
  have hforward := C.isIntegral_apply_of_twoPair_normalizedDistance T
    g₁ g₂ r₁ r₂ hr₂ a c b d hg₁a hg₁c hg₂b hg₂d hTb hTd
  have hbackward := C.isIntegral_symm_apply_of_twoPair_normalizedDistance T
    g₁ g₂ r₁ r₂ hr₁ a c b d hg₁a hg₁c hg₂b hg₂d hTb hTd
  let degreeRight := C.affineNormalizationRingAlgEquivOfFunctionFieldAlgEquiv
    T hforward hbackward
  refine ⟨degreeRight, ?_, ?_⟩
  · exact C.affineNormalizationRingAlgEquivOfFunctionFieldAlgEquiv_apply_lift
      T hforward hbackward (by simpa [squaredDistanceFunctionAt] using hTb)
  · exact C.affineNormalizationRingAlgEquivOfFunctionFieldAlgEquiv_apply_lift
      T hforward hbackward (by simpa [squaredDistanceFunctionAt] using hTd)

end IrreduciblePlanePolynomial

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open EuclideanGeometry PachDeZeeuw.Algebraic

variable {n : ℕ}


theorem circleEquationPolynomial_totalDegree_eq (c : _root_.Point2) (r : ℝ) :
    (circleEquationPolynomial c r).totalDegree = 2 := by
  apply le_antisymm
  · have hconstant :
        (MvPolynomial.C (r ^ 2) : PlanePoly).totalDegree ≤ 2 := by
      rw [MvPolynomial.totalDegree_C]
      omega
    exact (MvPolynomial.totalDegree_sub _ _).trans
      (max_le (planeSquaredDistancePolynomial_totalDegree_le c) hconstant)
  · have htop :
        MvPolynomial.homogeneousComponent 2 (circleEquationPolynomial c r) ≠ 0 := by
      have hconstant :
          MvPolynomial.homogeneousComponent 2
              (MvPolynomial.C (r ^ 2) : PlanePoly) = 0 := by
        apply MvPolynomial.homogeneousComponent_eq_zero
        rw [MvPolynomial.totalDegree_C]
        omega
      rw [circleEquationPolynomial, map_sub,
        homogeneousComponent_two_planeSquaredDistancePolynomial, hconstant, sub_zero]
      exact planeRadialQuadratic_ne_zero
    by_contra hdegree
    apply htop
    apply MvPolynomial.homogeneousComponent_eq_zero
    omega


end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open EuclideanGeometry PachDeZeeuw PachDeZeeuw.Algebraic


@[simp]
theorem mem_selfCurveSingularAnchors {d : ℕ}
    (X : PreparedBipartiteInput d) (p : X.P₁) :
    p ∈ selfCurveSingularAnchors X ↔
      (p : PachDeZeeuw.Algebraic.Point2) ∈
        SingularPointSet (preparedSecondCurvePolynomial X) := by
  classical
  simp [selfCurveSingularAnchors]


@[simp]
theorem mem_selfCurveExceptionalAnchors {d : ℕ}
    (X : PreparedBipartiteInput d) (axisAnchors : Finset X.P₁) (p : X.P₁) :
    p ∈ selfCurveExceptionalAnchors X axisAnchors ↔
      (p : PachDeZeeuw.Algebraic.Point2) ∈
        SingularPointSet (preparedSecondCurvePolynomial X) ∨
        p ∈ axisAnchors := by
  classical
  simp [selfCurveExceptionalAnchors]

 
theorem not_mem_singularPointSet_of_not_mem_selfCurveExceptionalAnchors
    {d : ℕ} (X : PreparedBipartiteInput d) (axisAnchors : Finset X.P₁)
    (p : X.P₁) (hp : p ∉ selfCurveExceptionalAnchors X axisAnchors) :
    (p : PachDeZeeuw.Algebraic.Point2) ∉
      SingularPointSet (preparedSecondCurvePolynomial X) := by
  intro hsingular
  apply hp
  exact (mem_selfCurveExceptionalAnchors X axisAnchors p).2 (Or.inl hsingular)


theorem selfCurveAnchor_mem_preparedSecondCurve_zeroSet
    {d : ℕ} {X : PreparedBipartiteInput d}
    (hself : SelfCurvePreparedInput X) (p : X.P₁) :
    (p : PachDeZeeuw.Algebraic.Point2) ∈
      PlaneCurveZeroSet (preparedSecondCurvePolynomial X) := by
  have hp : (p : PachDeZeeuw.Algebraic.Point2) ∈ X.C₁ := X.hP₁ p.property
  rw [hself, preparedSecondCurvePolynomial_zeroSet X] at hp
  exact hp


theorem anchors_not_mem_of_label_not_mem_selfCurveDeletedLabels
    {d : ℕ} {X : PreparedBipartiteInput d}
    {degreeRight : Finset X.P₁} {Γ : Finset (X.P₁ × X.P₁)}
    {ij : X.P₁ × X.P₁} (hij : ij ∉ selfCurveDeletedLabels X degreeRight Γ) :
    ij.1 ∉ degreeRight ∧ ij.2 ∉ degreeRight ∧ ij ∉ Γ := by
  classical
  simpa [selfCurveDeletedLabels, deletedIndexedPairs, exceptionalOrderedPairs] using hij


end Esgk

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

namespace IrreduciblePlanePolynomial


namespace RealAffineNormalizationPoint


@[simp]
theorem comap_apply {C : IrreduciblePlanePolynomial ℝ}
    (x : C.RealAffineNormalizationPoint)
    (degreeRight : C.affineNormalizationRing ≃ₐ[ℝ] C.affineNormalizationRing)
    (z : C.affineNormalizationRing) :
    x.comap degreeRight z = x (degreeRight z) :=
  rfl


theorem apply_affineNormalizationLift_squaredDistanceClassAt
    {C : IrreduciblePlanePolynomial ℝ}
    (x : C.RealAffineNormalizationPoint) (a : PachDeZeeuw.Algebraic.Point2) :
    x (C.affineNormalizationLift (C.squaredDistanceClassAt a)) =
      dist x.basePoint a ^ 2 := by
  let ψ : C.CoordinateRing →+* ℝ :=
    x.toRingHom.comp (algebraMap C.CoordinateRing C.affineNormalizationRing)
  have hclass :
      C.squaredDistanceClassAt a =
        (C.coordinateClass 0 - algebraMap ℝ C.CoordinateRing (a 0)) ^ 2 +
          (C.coordinateClass 1 - algebraMap ℝ C.CoordinateRing (a 1)) ^ 2 := by
    simp [squaredDistanceClassAt, planeSquaredDistancePolynomial, coordinateClass]
    rw [← MvPolynomial.algebraMap_eq]
    rw [Ideal.Quotient.mk_algebraMap]
    rw [Ideal.Quotient.mk_algebraMap]
  have hψ_coordinate (i : Fin 2) : ψ (C.coordinateClass i) = x.basePoint i := rfl
  have hψ_scalar (r : ℝ) : ψ (algebraMap ℝ C.CoordinateRing r) = r := by
    change x (algebraMap ℝ C.affineNormalizationRing r) = r
    exact x.commutes r
  change ψ (C.squaredDistanceClassAt a) = dist x.basePoint a ^ 2
  rw [hclass]
  simp only [map_add, map_pow, map_sub]
  rw [hψ_coordinate, hψ_coordinate, hψ_scalar, hψ_scalar]
  rw [EuclideanSpace.dist_sq_eq]
  simp [Fin.sum_univ_two, Real.dist_eq]


theorem comap_basePoint_eq_of_lift_squaredDistanceClassAt_eq
    {C : IrreduciblePlanePolynomial ℝ}
    (degreeRight : C.affineNormalizationRing ≃ₐ[ℝ] C.affineNormalizationRing)
    (x : C.RealAffineNormalizationPoint) {a b : PachDeZeeuw.Algebraic.Point2}
    (hxa : x.basePoint = a)
    (hEba : degreeRight (C.affineNormalizationLift (C.squaredDistanceClassAt b)) =
      C.affineNormalizationLift (C.squaredDistanceClassAt a)) :
    (x.comap degreeRight).basePoint = b := by
  apply anchor_image_eq_of_sqDistance_pullback hxa
  intro y
  rw [← y.apply_affineNormalizationLift_squaredDistanceClassAt]
  rw [← (y.comap degreeRight).apply_affineNormalizationLift_squaredDistanceClassAt]
  simp [hEba]


theorem dist_eq_of_two_lift_squaredDistanceClassAt_eq
    {C : IrreduciblePlanePolynomial ℝ}
    (degreeRight : C.affineNormalizationRing ≃ₐ[ℝ] C.affineNormalizationRing)
    (x : C.RealAffineNormalizationPoint) {a c b d : PachDeZeeuw.Algebraic.Point2}
    (hxa : x.basePoint = a)
    (hEba : degreeRight (C.affineNormalizationLift (C.squaredDistanceClassAt b)) =
      C.affineNormalizationLift (C.squaredDistanceClassAt a))
    (hEdc : degreeRight (C.affineNormalizationLift (C.squaredDistanceClassAt d)) =
      C.affineNormalizationLift (C.squaredDistanceClassAt c)) :
    dist a c = dist b d := by
  have hxb : (x.comap degreeRight).basePoint = b :=
    x.comap_basePoint_eq_of_lift_squaredDistanceClassAt_eq degreeRight hxa hEba
  have hsq : dist a c ^ 2 = dist b d ^ 2 := by
    calc
      dist a c ^ 2 =
          x (C.affineNormalizationLift (C.squaredDistanceClassAt c)) := by
        rw [← hxa]
        exact (x.apply_affineNormalizationLift_squaredDistanceClassAt c).symm
      _ = x (degreeRight (C.affineNormalizationLift (C.squaredDistanceClassAt d))) := by
        rw [hEdc]
      _ = (x.comap degreeRight)
          (C.affineNormalizationLift (C.squaredDistanceClassAt d)) := rfl
      _ = dist (x.comap degreeRight).basePoint d ^ 2 :=
        (x.comap degreeRight).apply_affineNormalizationLift_squaredDistanceClassAt d
      _ = dist b d ^ 2 := by rw [hxb]
  nlinarith [show 0 ≤ dist a c from dist_nonneg,
    show 0 ≤ dist b d from dist_nonneg]


theorem exists_comap_basePoint_eq_and_dist_eq_of_infinite_intersection
    (C : IrreduciblePlanePolynomial ℝ)
    (g₁ g₂ : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) {r₁ r₂ : ℝ}
    (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0)
    (hns₁ :
      xAxisReflectionPoint ''
          PlaneCurveZeroSet (C.affineIsometryTransport g₁).polynomial ≠
        PlaneCurveZeroSet (C.affineIsometryTransport g₁).polynomial)
    (hns₂ :
      xAxisReflectionPoint ''
          PlaneCurveZeroSet (C.affineIsometryTransport g₂).polynomial ≠
        PlaneCurveZeroSet (C.affineIsometryTransport g₂).polynomial)
    (a c b d : PachDeZeeuw.Algebraic.Point2)
    (hg₁a : g₁ a = xAxisPoint (-r₁))
    (hg₁c : g₁ c = xAxisPoint r₁)
    (hg₂b : g₂ b = xAxisPoint (-r₂))
    (hg₂d : g₂ d = xAxisPoint r₂)
    (hinf : (twoPairDistanceCommonZeroSet C a c b d).Infinite)
    (x : C.RealAffineNormalizationPoint) (hxa : x.basePoint = a) :
    ∃ degreeRight : C.affineNormalizationRing ≃ₐ[ℝ] C.affineNormalizationRing,
      (x.comap degreeRight).basePoint = b ∧ dist a c = dist b d := by
  obtain ⟨degreeRight, hEba, hEdc⟩ :=
    C.exists_affineNormalizationRingAlgEquiv_of_infinite_intersection
      g₁ g₂ hr₁ hr₂ hns₁ hns₂ a c b d hg₁a hg₁c hg₂b hg₂d hinf
  exact ⟨degreeRight, x.comap_basePoint_eq_of_lift_squaredDistanceClassAt_eq degreeRight hxa hEba,
    x.dist_eq_of_two_lift_squaredDistanceClassAt_eq degreeRight hxa hEba hEdc⟩

end RealAffineNormalizationPoint

end IrreduciblePlanePolynomial

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open MvPolynomial
open PachDeZeeuw.Algebraic

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__circularChart_C_half_mul_two :
    (MvPolynomial.C (1 / 2 : ℂ) : CircularChartPoly) * 2 = 1 := by
  change MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.C (2 : ℂ) = MvPolynomial.C 1
  rw [← map_mul]
  norm_num

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__circularChart_C_I_sq :
    (MvPolynomial.C Complex.I : CircularChartPoly) ^ 2 = -1 := by
  rw [← map_pow, Complex.I_sq, map_neg, map_one]


theorem isotropicAffineCircularChartI_planeToIsotropic_realToComplex
    (G : PlanePoly) :
    isotropicAffineCircularChartI
        (planeToIsotropicCoordinates (realToComplexPlanePolynomial G)) =
      affineCircularChartI G := by
  change
    (((isotropicAffineCircularChartI.comp planeToIsotropicCoordinates).comp
      realToComplexPlanePolynomial) G) = affineCircularChartI G
  apply RingHom.congr_fun
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [isotropicAffineCircularChartI, planeToIsotropicCoordinates,
      realToComplexPlanePolynomial, affineCircularChartI, affineCircularChart]
  · intro i
    fin_cases i <;>
      simp [isotropicAffineCircularChartI, planeToIsotropicCoordinates,
        realToComplexPlanePolynomial, affineCircularChartI, affineCircularChart,
        circularChartU]
    · simpa [mul_assoc] using inline_Esgk_MaximallyCircularIsotropicBidegree__circularChart_C_half_mul_two
    · calc
        _ = (MvPolynomial.C Complex.I + circularChartU) *
            ((MvPolynomial.C (1 / 2 : ℂ) : CircularChartPoly) * 2) := by
          simp only [circularChartU]
          ring_nf
          rw [inline_Esgk_MaximallyCircularIsotropicBidegree__circularChart_C_I_sq]
          ring
        _ = MvPolynomial.C Complex.I + circularChartU := by
          rw [inline_Esgk_MaximallyCircularIsotropicBidegree__circularChart_C_half_mul_two, mul_one]


theorem isotropicAffineCircularChartJ_planeToIsotropic_realToComplex
    (G : PlanePoly) :
    isotropicAffineCircularChartJ
        (planeToIsotropicCoordinates (realToComplexPlanePolynomial G)) =
      affineCircularChartJ G := by
  change
    (((isotropicAffineCircularChartJ.comp planeToIsotropicCoordinates).comp
      realToComplexPlanePolynomial) G) = affineCircularChartJ G
  apply RingHom.congr_fun
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [isotropicAffineCircularChartJ, planeToIsotropicCoordinates,
      realToComplexPlanePolynomial, affineCircularChartJ, affineCircularChart]
  · intro i
    fin_cases i <;>
      simp [isotropicAffineCircularChartJ, planeToIsotropicCoordinates,
        realToComplexPlanePolynomial, affineCircularChartJ, affineCircularChart,
        circularChartU]
    · simpa [mul_assoc] using inline_Esgk_MaximallyCircularIsotropicBidegree__circularChart_C_half_mul_two
    · calc
        _ = (-MvPolynomial.C Complex.I + circularChartU) *
            ((MvPolynomial.C (1 / 2 : ℂ) : CircularChartPoly) * 2) := by
          simp only [circularChartU]
          ring_nf
          rw [inline_Esgk_MaximallyCircularIsotropicBidegree__circularChart_C_I_sq]
          ring
        _ = -MvPolynomial.C Complex.I + circularChartU := by
          rw [inline_Esgk_MaximallyCircularIsotropicBidegree__circularChart_C_half_mul_two, mul_one]

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__planeToIsotropicCoordinates_isHomogeneous
    {d : ℕ} {P : ComplexPlanePoly} (hP : P.IsHomogeneous d) :
    (planeToIsotropicCoordinates P).IsHomogeneous d := by
  change
    (MvPolynomial.eval₂ (MvPolynomial.C : ℂ →+* ComplexPlanePoly)
      ![MvPolynomial.C (1 / 2 : ℂ) * (MvPolynomial.X 0 + MvPolynomial.X 1),
        MvPolynomial.C (1 / (2 * Complex.I)) *
          (MvPolynomial.X 0 - MvPolynomial.X 1)] P).IsHomogeneous d
  have h := hP.eval₂
    (MvPolynomial.C : ℂ →+* ComplexPlanePoly)
    ![MvPolynomial.C (1 / 2 : ℂ) * (MvPolynomial.X 0 + MvPolynomial.X 1),
      MvPolynomial.C (1 / (2 * Complex.I)) *
        (MvPolynomial.X 0 - MvPolynomial.X 1)]
    (fun c ↦ MvPolynomial.isHomogeneous_C (Fin 2) c)
    (fun i ↦ by
      fin_cases i
      · exact ((MvPolynomial.isHomogeneous_X ℂ 0).add
          (MvPolynomial.isHomogeneous_X ℂ 1)).C_mul _
      · exact ((MvPolynomial.isHomogeneous_X ℂ 0).sub
          (MvPolynomial.isHomogeneous_X ℂ 1)).C_mul _)
  rw [Nat.one_mul] at h
  exact h

 
theorem planeToIsotropicCoordinates_homogeneousComponent
    (d : ℕ) (P : ComplexPlanePoly) :
    planeToIsotropicCoordinates (MvPolynomial.homogeneousComponent d P) =
      MvPolynomial.homogeneousComponent d (planeToIsotropicCoordinates P) := by
  classical
  by_cases hd : d ≤ P.totalDegree
  · have hsum :
        ∑ k ∈ Finset.range (P.totalDegree + 1),
            planeToIsotropicCoordinates (MvPolynomial.homogeneousComponent k P) =
          planeToIsotropicCoordinates P := by
      rw [← map_sum, MvPolynomial.sum_homogeneousComponent]
    have himage (k : ℕ) :
        (planeToIsotropicCoordinates
          (MvPolynomial.homogeneousComponent k P)).IsHomogeneous k :=
      inline_Esgk_MaximallyCircularIsotropicBidegree__planeToIsotropicCoordinates_isHomogeneous
        (MvPolynomial.homogeneousComponent_isHomogeneous k P)
    symm
    calc
      MvPolynomial.homogeneousComponent d (planeToIsotropicCoordinates P) =
          MvPolynomial.homogeneousComponent d
            (∑ k ∈ Finset.range (P.totalDegree + 1),
              planeToIsotropicCoordinates (MvPolynomial.homogeneousComponent k P)) := by
        rw [hsum]
      _ = ∑ k ∈ Finset.range (P.totalDegree + 1),
          MvPolynomial.homogeneousComponent d
            (planeToIsotropicCoordinates (MvPolynomial.homogeneousComponent k P)) := by
        simp only [map_sum]
      _ = planeToIsotropicCoordinates (MvPolynomial.homogeneousComponent d P) := by
        simp_rw [MvPolynomial.homogeneousComponent_of_mem (himage _)]
        simp [hd]
  · have hPd : P.totalDegree < d := by omega
    have hTd : (planeToIsotropicCoordinates P).totalDegree < d := by
      rw [planeToIsotropicCoordinates_totalDegree]
      exact hPd
    rw [MvPolynomial.homogeneousComponent_eq_zero d P hPd, map_zero,
      MvPolynomial.homogeneousComponent_eq_zero d _ hTd]

 
theorem realToComplexPlanePolynomial_homogeneousComponent
    (d : ℕ) (G : PlanePoly) :
    realToComplexPlanePolynomial (MvPolynomial.homogeneousComponent d G) =
      MvPolynomial.homogeneousComponent d (realToComplexPlanePolynomial G) := by
  ext e
  simp only [realToComplexPlanePolynomial, MvPolynomial.coeff_map,
    MvPolynomial.coeff_homogeneousComponent]
  split_ifs <;> simp


theorem projectiveCircularChartI_planeHomogenization_eq_isotropic
    (D : ℕ) (G : PlanePoly) :
    projectiveCircularChartI (planeHomogenization D G) =
      isotropicHomogenizedCircularChartI D
        (planeToIsotropicCoordinates (realToComplexPlanePolynomial G)) := by
  rw [projectiveCircularChartI, projectiveCircularChart_planeHomogenization]
  rw [isotropicHomogenizedCircularChartI]
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  change affineCircularChartI (MvPolynomial.homogeneousComponent d G) = _
  rw [← isotropicAffineCircularChartI_planeToIsotropic_realToComplex]
  congr 1
  rw [realToComplexPlanePolynomial_homogeneousComponent,
    planeToIsotropicCoordinates_homogeneousComponent]

 
theorem projectiveCircularChartJ_planeHomogenization_eq_isotropic
    (D : ℕ) (G : PlanePoly) :
    projectiveCircularChartJ (planeHomogenization D G) =
      isotropicHomogenizedCircularChartJ D
        (planeToIsotropicCoordinates (realToComplexPlanePolynomial G)) := by
  rw [projectiveCircularChartJ, projectiveCircularChart_planeHomogenization]
  rw [isotropicHomogenizedCircularChartJ]
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  change affineCircularChartJ (MvPolynomial.homogeneousComponent d G) = _
  rw [← isotropicAffineCircularChartJ_planeToIsotropic_realToComplex]
  congr 1
  rw [realToComplexPlanePolynomial_homogeneousComponent,
    planeToIsotropicCoordinates_homogeneousComponent]

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__homogenized_eval₂_eq_support_sum
    (D : ℕ) (Q : ComplexPlanePoly) (A B : CircularChartPoly)
    (hdegree : Q.totalDegree ≤ D) :
    (∑ d ∈ Finset.range (D + 1),
      circularChartZ ^ (D - d) *
        MvPolynomial.eval₂Hom (MvPolynomial.C : ℂ →+* CircularChartPoly) ![A, B]
          (MvPolynomial.homogeneousComponent d Q)) =
      ∑ e ∈ Q.support,
        MvPolynomial.C (MvPolynomial.coeff e Q) * A ^ e 0 * B ^ e 1 *
          circularChartZ ^ (D - e.degree) := by
  classical
  calc
    _ = ∑ d ∈ Finset.range (D + 1),
        ∑ e ∈ Q.support with e.degree = d,
          MvPolynomial.C (MvPolynomial.coeff e Q) * A ^ e 0 * B ^ e 1 *
            circularChartZ ^ (D - e.degree) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [MvPolynomial.homogeneousComponent_apply, map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      have hedegree : e.degree = d := (Finset.mem_filter.mp he).2
      rw [MvPolynomial.eval₂Hom_monomial]
      rw [hedegree]
      simp [Finsupp.prod_fintype, Fin.prod_univ_two]
      ring
    _ = ∑ e ∈ Q.support,
        MvPolynomial.C (MvPolynomial.coeff e Q) * A ^ e 0 * B ^ e 1 *
          circularChartZ ^ (D - e.degree) := by
      apply Finset.sum_fiberwise_of_maps_to
      intro e he
      rw [Finsupp.degree_eq_sum]
      simp only [Finset.mem_range, Nat.lt_add_one_iff]
      calc
        ∑ i, e i = e.sum (fun _ a ↦ a) :=
          (Finsupp.sum_fintype e (fun _ a ↦ a) (fun _ ↦ rfl)).symm
        _ ≤ D := (MvPolynomial.le_totalDegree he).trans hdegree

 
theorem isotropicHomogenizedCircularChartI_eq_support_sum
    (D : ℕ) (Q : ComplexPlanePoly) (hdegree : Q.totalDegree ≤ D) :
    isotropicHomogenizedCircularChartI D Q =
      ∑ e ∈ Q.support,
        MvPolynomial.C (MvPolynomial.coeff e Q) *
          (MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
          (2 - MvPolynomial.C Complex.I * circularChartU) ^ e 1 *
          circularChartZ ^ (D - e.degree) := by
  rw [isotropicHomogenizedCircularChartI]
  exact inline_Esgk_MaximallyCircularIsotropicBidegree__homogenized_eval₂_eq_support_sum D Q _ _ hdegree

 
theorem isotropicHomogenizedCircularChartJ_eq_support_sum
    (D : ℕ) (Q : ComplexPlanePoly) (hdegree : Q.totalDegree ≤ D) :
    isotropicHomogenizedCircularChartJ D Q =
      ∑ e ∈ Q.support,
        MvPolynomial.C (MvPolynomial.coeff e Q) *
          (2 + MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
          (-MvPolynomial.C Complex.I * circularChartU) ^ e 1 *
          circularChartZ ^ (D - e.degree) := by
  rw [isotropicHomogenizedCircularChartJ]
  exact inline_Esgk_MaximallyCircularIsotropicBidegree__homogenized_eval₂_eq_support_sum D Q _ _ hdegree


@[simp]
theorem isotropicILeadingExponent_zero (D : ℕ) (e : Fin 2 →₀ ℕ) :
    isotropicILeadingExponent D e 0 = e 0 := by
  simp [isotropicILeadingExponent]

@[simp]
theorem isotropicILeadingExponent_one (D : ℕ) (e : Fin 2 →₀ ℕ) :
    isotropicILeadingExponent D e 1 = D - e.degree := by
  simp [isotropicILeadingExponent]

@[simp]
theorem isotropicJLeadingExponent_zero (D : ℕ) (e : Fin 2 →₀ ℕ) :
    isotropicJLeadingExponent D e 0 = e 1 := by
  simp [isotropicJLeadingExponent]

@[simp]
theorem isotropicJLeadingExponent_one (D : ℕ) (e : Fin 2 →₀ ℕ) :
    isotropicJLeadingExponent D e 1 = D - e.degree := by
  simp [isotropicJLeadingExponent]

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add (e : Fin 2 →₀ ℕ) :
    e.degree = e 0 + e 1 := by
  simp [Finsupp.degree_eq_sum, Fin.sum_univ_two]

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicILeadingExponent_degree
    (D : ℕ) (e : Fin 2 →₀ ℕ) (he : e.degree ≤ D) :
    (isotropicILeadingExponent D e).degree = D - e 1 := by
  rw [inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add e] at he
  rw [inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add, isotropicILeadingExponent_zero,
    isotropicILeadingExponent_one, inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add e]
  omega

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicJLeadingExponent_degree
    (D : ℕ) (e : Fin 2 →₀ ℕ) (he : e.degree ≤ D) :
    (isotropicJLeadingExponent D e).degree = D - e 0 := by
  rw [inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add e] at he
  rw [inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add, isotropicJLeadingExponent_zero,
    isotropicJLeadingExponent_one, inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add e]
  omega

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__coordinate_pow_exponent_le_of_dvd_of_mem_support
    {P : CircularChartPoly} {m : Fin 2 →₀ ℕ} {i : Fin 2} {n : ℕ}
    (hm : m ∈ P.support) (hdvd : MvPolynomial.X i ^ n ∣ P) : n ≤ m i := by
  rcases hdvd with ⟨R, rfl⟩
  have hcoeff : MvPolynomial.coeff m (MvPolynomial.X i ^ n * R) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hm
  rw [MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.coeff_monomial_mul'] at hcoeff
  split at hcoeff
  next hle =>
    have := hle i
    simpa using this
  next hnot => exact (hcoeff rfl).elim

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__circularChartITerm_degreeOf_one_le
    (D : ℕ) (e : Fin 2 →₀ ℕ) (c : ℂ) :
    MvPolynomial.degreeOf 1 (isotropicCircularChartITerm D e c) ≤ D - e.degree := by
  have hU : MvPolynomial.degreeOf 1
      (MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) ≤ 0 := by
    simpa [circularChartU, MvPolynomial.degreeOf_X, show (1 : Fin 2) ≠ 0 by decide]
      using MvPolynomial.degreeOf_mul_le 1
        (MvPolynomial.C Complex.I : CircularChartPoly) circularChartU
  have hV : MvPolynomial.degreeOf 1
      (2 - MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) ≤ 0 := by
    exact (MvPolynomial.degreeOf_sub_le 1 (2 : CircularChartPoly)
      (MvPolynomial.C Complex.I * circularChartU)).trans
        (max_le (by
          change MvPolynomial.degreeOf 1
            (MvPolynomial.C (2 : ℂ) : CircularChartPoly) ≤ 0
          simp) hU)
  have hUpow := MvPolynomial.degreeOf_pow_le 1
    (MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) (e 0)
  have hVpow := MvPolynomial.degreeOf_pow_le 1
    (2 - MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) (e 1)
  have hleft := MvPolynomial.degreeOf_mul_le 1
    (MvPolynomial.C c : CircularChartPoly)
    ((MvPolynomial.C Complex.I * circularChartU) ^ e 0)
  have hmiddle := MvPolynomial.degreeOf_mul_le 1
    (MvPolynomial.C c * (MvPolynomial.C Complex.I * circularChartU) ^ e 0)
    ((2 - MvPolynomial.C Complex.I * circularChartU) ^ e 1)
  have hZpow := MvPolynomial.degreeOf_pow_le 1 circularChartZ (D - e.degree)
  have hall := MvPolynomial.degreeOf_mul_le 1
    (MvPolynomial.C c * (MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
      (2 - MvPolynomial.C Complex.I * circularChartU) ^ e 1)
    (circularChartZ ^ (D - e.degree))
  have hUpowZero : MvPolynomial.degreeOf 1
      ((MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) ^ e 0) ≤ 0 := by
    rw [Nat.le_zero]
    rw [Nat.le_zero] at hU
    simpa [hU] using hUpow
  have hVpowZero : MvPolynomial.degreeOf 1
      ((2 - MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) ^ e 1) ≤ 0 := by
    rw [Nat.le_zero]
    rw [Nat.le_zero] at hV
    simpa [hV] using hVpow
  have hleftZero : MvPolynomial.degreeOf 1
      (MvPolynomial.C c * (MvPolynomial.C Complex.I * circularChartU) ^ e 0) ≤ 0 := by
    rw [Nat.le_zero] at hUpowZero ⊢
    simpa [hUpowZero] using hleft
  have hmiddleZero : MvPolynomial.degreeOf 1
      (MvPolynomial.C c * (MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
        (2 - MvPolynomial.C Complex.I * circularChartU) ^ e 1) ≤ 0 := by
    rw [Nat.le_zero] at hleftZero hVpowZero ⊢
    simpa [hleftZero, hVpowZero] using hmiddle
  have hZpowBound : MvPolynomial.degreeOf 1
      (circularChartZ ^ (D - e.degree)) ≤ D - e.degree := by
    simpa [circularChartZ] using hZpow
  change MvPolynomial.degreeOf 1
    (MvPolynomial.C c * (MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
      (2 - MvPolynomial.C Complex.I * circularChartU) ^ e 1 *
      circularChartZ ^ (D - e.degree)) ≤ D - e.degree
  simpa using hall.trans (Nat.add_le_add hmiddleZero hZpowBound)

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicCircularChartITerm_coordinate_bounds
    (D : ℕ) (e m : Fin 2 →₀ ℕ) (c : ℂ)
    (hm : m ∈ (isotropicCircularChartITerm D e c).support) :
    e 0 ≤ m 0 ∧ m 1 = D - e.degree := by
  have hUdvd : circularChartU ^ e 0 ∣ isotropicCircularChartITerm D e c := by
    refine ⟨MvPolynomial.C c * MvPolynomial.C (Complex.I ^ e 0) *
      (2 - MvPolynomial.C Complex.I * circularChartU) ^ e 1 *
      circularChartZ ^ (D - e.degree), ?_⟩
    rw [isotropicCircularChartITerm, mul_pow, ← map_pow]
    ring
  have hZdvd : circularChartZ ^ (D - e.degree) ∣ isotropicCircularChartITerm D e c := by
    refine ⟨MvPolynomial.C c * (MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
      (2 - MvPolynomial.C Complex.I * circularChartU) ^ e 1, ?_⟩
    rw [isotropicCircularChartITerm]
    ring
  have hzero : e 0 ≤ m 0 := by
    apply inline_Esgk_MaximallyCircularIsotropicBidegree__coordinate_pow_exponent_le_of_dvd_of_mem_support hm
    simpa [circularChartU] using hUdvd
  have honeLower : D - e.degree ≤ m 1 := by
    apply inline_Esgk_MaximallyCircularIsotropicBidegree__coordinate_pow_exponent_le_of_dvd_of_mem_support hm
    simpa [circularChartZ] using hZdvd
  have honeUpper : m 1 ≤ D - e.degree :=
    (MvPolynomial.le_degreeOf_of_mem_support 1 hm).trans
      (inline_Esgk_MaximallyCircularIsotropicBidegree__circularChartITerm_degreeOf_one_le D e c)
  exact ⟨hzero, Nat.le_antisymm honeUpper honeLower⟩

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicCircularChartITerm_coeff_leading
    (D : ℕ) (e : Fin 2 →₀ ℕ) (c : ℂ) :
    MvPolynomial.coeff (isotropicILeadingExponent D e)
        (isotropicCircularChartITerm D e c) =
      c * Complex.I ^ e 0 * (2 : ℂ) ^ e 1 := by
  classical
  rw [isotropicCircularChartITerm]
  change MvPolynomial.coeff
    (Finsupp.single 0 (e 0) + Finsupp.single 1 (D - e.degree))
    (MvPolynomial.C c * (MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
      (2 - MvPolynomial.C Complex.I * circularChartU) ^ e 1 *
      circularChartZ ^ (D - e.degree)) = _
  rw [circularChartZ, MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.coeff_mul_monomial, mul_one]
  rw [mul_pow, ← map_pow, circularChartU, MvPolynomial.X_pow_eq_monomial]
  simp only [← mul_assoc, MvPolynomial.C_mul_monomial]
  rw [MvPolynomial.coeff_monomial_mul']
  simp only [le_refl, if_true, tsub_self]
  rw [← MvPolynomial.constantCoeff_eq, map_pow]
  have htwo : MvPolynomial.constantCoeff (2 : CircularChartPoly) = (2 : ℂ) := by
    change MvPolynomial.constantCoeff
      (MvPolynomial.C (2 : ℂ) : CircularChartPoly) = (2 : ℂ)
    simp
  rw [map_sub, map_mul, htwo, MvPolynomial.constantCoeff_C,
    MvPolynomial.constantCoeff_X, mul_zero, sub_zero]
  ring

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicHomogenizedCircularChartI_coeff_extremal
    (D : ℕ) (Q : ComplexPlanePoly) (e : Fin 2 →₀ ℕ)
    (hdegree : Q.totalDegree ≤ D) (he : e ∈ Q.support)
    (hmax : ∀ f ∈ Q.support, f 1 ≤ e 1) :
    MvPolynomial.coeff (isotropicILeadingExponent D e)
        (isotropicHomogenizedCircularChartI D Q) =
      MvPolynomial.coeff e Q * Complex.I ^ e 0 * (2 : ℂ) ^ e 1 := by
  classical
  rw [isotropicHomogenizedCircularChartI_eq_support_sum D Q hdegree]
  rw [MvPolynomial.coeff_sum]
  calc
    _ = MvPolynomial.coeff (isotropicILeadingExponent D e)
        (MvPolynomial.C (MvPolynomial.coeff e Q) *
          (MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
          (2 - MvPolynomial.C Complex.I * circularChartU) ^ e 1 *
          circularChartZ ^ (D - e.degree)) := by
      apply Finset.sum_eq_single e
      · intro f hf hfe
        have hfzero : MvPolynomial.coeff (isotropicILeadingExponent D e)
            (isotropicCircularChartITerm D f (MvPolynomial.coeff f Q)) = 0 := by
          by_contra hcoeff
          have hmem : isotropicILeadingExponent D e ∈
              (isotropicCircularChartITerm D f (MvPolynomial.coeff f Q)).support :=
            MvPolynomial.mem_support_iff.mpr hcoeff
          obtain ⟨hzero, hone⟩ :=
            inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicCircularChartITerm_coordinate_bounds D f
              (isotropicILeadingExponent D e) (MvPolynomial.coeff f Q) hmem
          have hfdegree : f.degree ≤ D :=
            (MvPolynomial.le_totalDegree hf).trans hdegree
          have hedegree : e.degree ≤ D :=
            (MvPolynomial.le_totalDegree he).trans hdegree
          have hdegreeEq : f.degree = e.degree := by
            rw [isotropicILeadingExponent_one] at hone
            omega
          have honeLe : f 1 ≤ e 1 := hmax f hf
          rw [isotropicILeadingExponent_zero] at hzero
          have hzeroEq : f 0 = e 0 := by
            rw [inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add f, inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add e] at hdegreeEq
            omega
          have honeEq : f 1 = e 1 := by
            rw [inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add f, inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add e] at hdegreeEq
            omega
          apply hfe
          apply Finsupp.ext
          intro i
          fin_cases i
          · exact hzeroEq
          · exact honeEq
        simpa [isotropicCircularChartITerm] using hfzero
      · intro hnot
        exact (hnot he).elim
    _ = _ := by
      simpa [isotropicCircularChartITerm] using
        inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicCircularChartITerm_coeff_leading D e (MvPolynomial.coeff e Q)

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__circularChartJTerm_degreeOf_one_le
    (D : ℕ) (e : Fin 2 →₀ ℕ) (c : ℂ) :
    MvPolynomial.degreeOf 1 (isotropicCircularChartJTerm D e c) ≤ D - e.degree := by
  have hU : MvPolynomial.degreeOf 1
      (MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) ≤ 0 := by
    simpa [circularChartU, MvPolynomial.degreeOf_X, show (1 : Fin 2) ≠ 0 by decide]
      using MvPolynomial.degreeOf_mul_le 1
        (MvPolynomial.C Complex.I : CircularChartPoly) circularChartU
  have hA : MvPolynomial.degreeOf 1
      (2 + MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) ≤ 0 := by
    exact (MvPolynomial.degreeOf_add_le 1 (2 : CircularChartPoly)
      (MvPolynomial.C Complex.I * circularChartU)).trans
        (max_le (by
          change MvPolynomial.degreeOf 1
            (MvPolynomial.C (2 : ℂ) : CircularChartPoly) ≤ 0
          simp) hU)
  have hB : MvPolynomial.degreeOf 1
      (-MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) ≤ 0 := by
    have hmul := MvPolynomial.degreeOf_mul_le 1
      (-MvPolynomial.C Complex.I : CircularChartPoly) circularChartU
    simpa [circularChartU, MvPolynomial.degreeOf_X,
      show (1 : Fin 2) ≠ 0 by decide] using hmul
  have hApow := MvPolynomial.degreeOf_pow_le 1
    (2 + MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) (e 0)
  have hBpow := MvPolynomial.degreeOf_pow_le 1
    (-MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) (e 1)
  have hleft := MvPolynomial.degreeOf_mul_le 1
    (MvPolynomial.C c : CircularChartPoly)
    ((2 + MvPolynomial.C Complex.I * circularChartU) ^ e 0)
  have hmiddle := MvPolynomial.degreeOf_mul_le 1
    (MvPolynomial.C c * (2 + MvPolynomial.C Complex.I * circularChartU) ^ e 0)
    ((-MvPolynomial.C Complex.I * circularChartU) ^ e 1)
  have hZpow := MvPolynomial.degreeOf_pow_le 1 circularChartZ (D - e.degree)
  have hall := MvPolynomial.degreeOf_mul_le 1
    (MvPolynomial.C c * (2 + MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
      (-MvPolynomial.C Complex.I * circularChartU) ^ e 1)
    (circularChartZ ^ (D - e.degree))
  have hApowZero : MvPolynomial.degreeOf 1
      ((2 + MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) ^ e 0) ≤ 0 := by
    rw [Nat.le_zero]
    rw [Nat.le_zero] at hA
    simpa [hA] using hApow
  have hBpowZero : MvPolynomial.degreeOf 1
      ((-MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) ^ e 1) ≤ 0 := by
    rw [Nat.le_zero]
    rw [Nat.le_zero] at hU
    simpa [hU] using hBpow
  have hleftZero : MvPolynomial.degreeOf 1
      (MvPolynomial.C c * (2 + MvPolynomial.C Complex.I * circularChartU) ^ e 0) ≤ 0 := by
    rw [Nat.le_zero] at hApowZero ⊢
    simpa [hApowZero] using hleft
  have hmiddleZero : MvPolynomial.degreeOf 1
      (MvPolynomial.C c * (2 + MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
        (-MvPolynomial.C Complex.I * circularChartU) ^ e 1) ≤ 0 := by
    simpa using hmiddle.trans (Nat.add_le_add hleftZero hBpowZero)
  have hZpowBound : MvPolynomial.degreeOf 1
      (circularChartZ ^ (D - e.degree)) ≤ D - e.degree := by
    simpa [circularChartZ] using hZpow
  change MvPolynomial.degreeOf 1
    (MvPolynomial.C c * (2 + MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
      (-MvPolynomial.C Complex.I * circularChartU) ^ e 1 *
      circularChartZ ^ (D - e.degree)) ≤ D - e.degree
  simpa using hall.trans (Nat.add_le_add hmiddleZero hZpowBound)

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicCircularChartJTerm_coordinate_bounds
    (D : ℕ) (e m : Fin 2 →₀ ℕ) (c : ℂ)
    (hm : m ∈ (isotropicCircularChartJTerm D e c).support) :
    e 1 ≤ m 0 ∧ m 1 = D - e.degree := by
  have hUdvd : circularChartU ^ e 1 ∣ isotropicCircularChartJTerm D e c := by
    refine ⟨MvPolynomial.C c * MvPolynomial.C ((-Complex.I) ^ e 1) *
      (2 + MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
      circularChartZ ^ (D - e.degree), ?_⟩
    rw [isotropicCircularChartJTerm, mul_pow, ← map_neg, ← map_pow]
    ring
  have hZdvd : circularChartZ ^ (D - e.degree) ∣ isotropicCircularChartJTerm D e c := by
    refine ⟨MvPolynomial.C c * (2 + MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
      (-MvPolynomial.C Complex.I * circularChartU) ^ e 1, ?_⟩
    rw [isotropicCircularChartJTerm]
    ring
  have hzero : e 1 ≤ m 0 := by
    apply inline_Esgk_MaximallyCircularIsotropicBidegree__coordinate_pow_exponent_le_of_dvd_of_mem_support hm
    simpa [circularChartU] using hUdvd
  have honeLower : D - e.degree ≤ m 1 := by
    apply inline_Esgk_MaximallyCircularIsotropicBidegree__coordinate_pow_exponent_le_of_dvd_of_mem_support hm
    simpa [circularChartZ] using hZdvd
  have honeUpper : m 1 ≤ D - e.degree :=
    (MvPolynomial.le_degreeOf_of_mem_support 1 hm).trans
      (inline_Esgk_MaximallyCircularIsotropicBidegree__circularChartJTerm_degreeOf_one_le D e c)
  exact ⟨hzero, Nat.le_antisymm honeUpper honeLower⟩

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicCircularChartJTerm_coeff_leading
    (D : ℕ) (e : Fin 2 →₀ ℕ) (c : ℂ) :
    MvPolynomial.coeff (isotropicJLeadingExponent D e)
        (isotropicCircularChartJTerm D e c) =
      c * (-Complex.I) ^ e 1 * (2 : ℂ) ^ e 0 := by
  classical
  rw [isotropicCircularChartJTerm]
  change MvPolynomial.coeff
    (Finsupp.single 0 (e 1) + Finsupp.single 1 (D - e.degree))
    (MvPolynomial.C c * (2 + MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
      (-MvPolynomial.C Complex.I * circularChartU) ^ e 1 *
      circularChartZ ^ (D - e.degree)) = _
  rw [circularChartZ, MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.coeff_mul_monomial, mul_one]
  have hneg : (-MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) =
      MvPolynomial.C (-Complex.I) * circularChartU := by
    rw [map_neg]
  rw [hneg, mul_pow, ← map_pow, circularChartU, MvPolynomial.X_pow_eq_monomial]
  have hreorder :
      (MvPolynomial.C c : CircularChartPoly) *
          (2 + MvPolynomial.C Complex.I * MvPolynomial.X (0 : Fin 2)) ^ e 0 *
          (MvPolynomial.C ((-Complex.I) ^ e 1) *
            MvPolynomial.monomial (Finsupp.single (0 : Fin 2) (e 1)) 1) =
        MvPolynomial.monomial (Finsupp.single (0 : Fin 2) (e 1))
            (c * (-Complex.I) ^ e 1) *
          (2 + MvPolynomial.C Complex.I * MvPolynomial.X (0 : Fin 2)) ^ e 0 := by
    calc
      _ = (MvPolynomial.C c * MvPolynomial.C ((-Complex.I) ^ e 1) *
            MvPolynomial.monomial (Finsupp.single (0 : Fin 2) (e 1)) 1) *
          (2 + MvPolynomial.C Complex.I * MvPolynomial.X (0 : Fin 2)) ^ e 0 := by ring
      _ = _ := by
        rw [← map_mul, MvPolynomial.C_mul_monomial]
        congr 2
        ring
  calc
    _ = MvPolynomial.coeff (Finsupp.single (0 : Fin 2) (e 1))
        (MvPolynomial.monomial (Finsupp.single (0 : Fin 2) (e 1))
            (c * (-Complex.I) ^ e 1) *
          (2 + MvPolynomial.C Complex.I * MvPolynomial.X 0) ^ e 0) :=
      congrArg (MvPolynomial.coeff (Finsupp.single (0 : Fin 2) (e 1))) hreorder
    _ = _ := by
      rw [MvPolynomial.coeff_monomial_mul']
      simp only [le_refl, if_true, tsub_self]
      rw [← MvPolynomial.constantCoeff_eq, map_pow]
      have htwo : MvPolynomial.constantCoeff (2 : CircularChartPoly) = (2 : ℂ) := by
        change MvPolynomial.constantCoeff
          (MvPolynomial.C (2 : ℂ) : CircularChartPoly) = (2 : ℂ)
        simp
      rw [map_add, map_mul, htwo, MvPolynomial.constantCoeff_C,
        MvPolynomial.constantCoeff_X, mul_zero, add_zero]

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicHomogenizedCircularChartJ_coeff_extremal
    (D : ℕ) (Q : ComplexPlanePoly) (e : Fin 2 →₀ ℕ)
    (hdegree : Q.totalDegree ≤ D) (he : e ∈ Q.support)
    (hmax : ∀ f ∈ Q.support, f 0 ≤ e 0) :
    MvPolynomial.coeff (isotropicJLeadingExponent D e)
        (isotropicHomogenizedCircularChartJ D Q) =
      MvPolynomial.coeff e Q * (-Complex.I) ^ e 1 * (2 : ℂ) ^ e 0 := by
  classical
  rw [isotropicHomogenizedCircularChartJ_eq_support_sum D Q hdegree]
  rw [MvPolynomial.coeff_sum]
  calc
    _ = MvPolynomial.coeff (isotropicJLeadingExponent D e)
        (MvPolynomial.C (MvPolynomial.coeff e Q) *
          (2 + MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
          (-MvPolynomial.C Complex.I * circularChartU) ^ e 1 *
          circularChartZ ^ (D - e.degree)) := by
      apply Finset.sum_eq_single e
      · intro f hf hfe
        have hfzero : MvPolynomial.coeff (isotropicJLeadingExponent D e)
            (isotropicCircularChartJTerm D f (MvPolynomial.coeff f Q)) = 0 := by
          by_contra hcoeff
          have hmem : isotropicJLeadingExponent D e ∈
              (isotropicCircularChartJTerm D f (MvPolynomial.coeff f Q)).support :=
            MvPolynomial.mem_support_iff.mpr hcoeff
          obtain ⟨hzero, hone⟩ :=
            inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicCircularChartJTerm_coordinate_bounds D f
              (isotropicJLeadingExponent D e) (MvPolynomial.coeff f Q) hmem
          have hfdegree : f.degree ≤ D :=
            (MvPolynomial.le_totalDegree hf).trans hdegree
          have hedegree : e.degree ≤ D :=
            (MvPolynomial.le_totalDegree he).trans hdegree
          have hdegreeEq : f.degree = e.degree := by
            rw [isotropicJLeadingExponent_one] at hone
            omega
          have hzeroLe : f 0 ≤ e 0 := hmax f hf
          rw [isotropicJLeadingExponent_zero] at hzero
          have hzeroEq : f 0 = e 0 := by
            rw [inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add f, inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add e] at hdegreeEq
            omega
          have honeEq : f 1 = e 1 := by
            rw [inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add f, inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add e] at hdegreeEq
            omega
          apply hfe
          apply Finsupp.ext
          intro i
          fin_cases i
          · exact hzeroEq
          · exact honeEq
        simpa [isotropicCircularChartJTerm] using hfzero
      · intro hnot
        exact (hnot he).elim
    _ = _ := by
      simpa [isotropicCircularChartJTerm] using
        inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicCircularChartJTerm_coeff_leading D e (MvPolynomial.coeff e Q)

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__planeCircularLocalOrder_le_degree_of_coeff_ne_zero
    (c : ℂ) {G : PlanePoly} {d : Fin 2 →₀ ℕ}
    (hcoeff : MvPolynomial.coeff d
        (projectiveCircularChart c (planeHomogenization G.totalDegree G)) ≠ 0) :
    planeCircularLocalOrder c G ≤ d.degree := by
  have hcoeffSeries : MvPowerSeries.coeff d
      ((projectiveCircularChart c (planeHomogenization G.totalDegree G) :
        CircularChartPoly) : MvPowerSeries (Fin 2) ℂ) ≠ 0 := by
    simpa using hcoeff
  have horder := MvPowerSeries.order_le hcoeffSeries
  have horderNat := ENat.toNat_le_toNat horder
  simpa [planeCircularLocalOrder, MvPolynomial.localOrder] using horderNat


theorem IsMaximallyCircular.bidegreeBound_planeIsotropicCoordinateEquiv
    {G : PlanePoly} (hmax : IsMaximallyCircular G) (hG : G ≠ 0)
    (p : ℕ) (hdegree : G.totalDegree = 2 * p) :
    BidegreeBound p
      (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)) := by
  classical
  let Q : ComplexPlanePoly :=
    planeToIsotropicCoordinates (realToComplexPlanePolynomial G)
  have hmapzero : realToComplexPlanePolynomial G ≠ 0 := by
    exact (MvPolynomial.map_injective Complex.ofRealHom Complex.ofReal_injective).ne hG
  have hQzero : Q ≠ 0 := by
    change planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G) ≠ 0
    exact planeIsotropicCoordinateEquiv.injective.ne hmapzero
  have hQdegree : Q.totalDegree ≤ G.totalDegree := by
    change (planeToIsotropicCoordinates
      (realToComplexPlanePolynomial G)).totalDegree ≤ G.totalDegree
    rw [planeToIsotropicCoordinates_totalDegree]
    change (MvPolynomial.map Complex.ofRealHom G).totalDegree ≤ G.totalDegree
    unfold MvPolynomial.totalDegree
    rw [MvPolynomial.support_map_of_injective G Complex.ofReal_injective]
  have hsupp : Q.support.Nonempty := MvPolynomial.support_nonempty.mpr hQzero
  obtain ⟨eI, heI, heIsup⟩ :=
    Finset.exists_mem_eq_sup Q.support hsupp (fun e : Fin 2 →₀ ℕ ↦ e 1)
  have heImax : ∀ f ∈ Q.support, f 1 ≤ eI 1 := by
    intro f hf
    calc
      f 1 ≤ Q.support.sup (fun e : Fin 2 →₀ ℕ ↦ e 1) :=
        Finset.le_sup (f := fun e : Fin 2 →₀ ℕ ↦ e 1) hf
      _ = eI 1 := heIsup
  obtain ⟨eJ, heJ, heJsup⟩ :=
    Finset.exists_mem_eq_sup Q.support hsupp (fun e : Fin 2 →₀ ℕ ↦ e 0)
  have heJmax : ∀ f ∈ Q.support, f 0 ≤ eJ 0 := by
    intro f hf
    calc
      f 0 ≤ Q.support.sup (fun e : Fin 2 →₀ ℕ ↦ e 0) :=
        Finset.le_sup (f := fun e : Fin 2 →₀ ℕ ↦ e 0) hf
      _ = eJ 0 := heJsup
  have heIdegree : eI.degree ≤ G.totalDegree :=
    (MvPolynomial.le_totalDegree heI).trans hQdegree
  have heJdegree : eJ.degree ≤ G.totalDegree :=
    (MvPolynomial.le_totalDegree heJ).trans hQdegree
  have hcoeffI : MvPolynomial.coeff
      (isotropicILeadingExponent G.totalDegree eI)
      (isotropicHomogenizedCircularChartI G.totalDegree Q) ≠ 0 := by
    rw [inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicHomogenizedCircularChartI_coeff_extremal
      G.totalDegree Q eI hQdegree heI heImax]
    exact mul_ne_zero
      (mul_ne_zero (MvPolynomial.mem_support_iff.mp heI)
        (pow_ne_zero _ Complex.I_ne_zero))
      (pow_ne_zero _ (by norm_num))
  have hchartCoeffI : MvPolynomial.coeff
      (isotropicILeadingExponent G.totalDegree eI)
      (projectiveCircularChart Complex.I
        (planeHomogenization G.totalDegree G)) ≠ 0 := by
    change MvPolynomial.coeff (isotropicILeadingExponent G.totalDegree eI)
      (projectiveCircularChartI (planeHomogenization G.totalDegree G)) ≠ 0
    rw [projectiveCircularChartI_planeHomogenization_eq_isotropic]
    exact hcoeffI
  have hlocalI := inline_Esgk_MaximallyCircularIsotropicBidegree__planeCircularLocalOrder_le_degree_of_coeff_ne_zero
    Complex.I hchartCoeffI
  rw [inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicILeadingExponent_degree G.totalDegree eI heIdegree] at hlocalI
  have horderI : planeCircularLocalOrderI G = p := by
    rcases hmax with ⟨hI, hJ⟩
    omega
  have heIbound : eI 1 ≤ p := by
    have heIcoord : eI 1 ≤ eI.degree := by
      rw [inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add]
      omega
    change planeCircularLocalOrderI G ≤ G.totalDegree - eI 1 at hlocalI
    rw [horderI, hdegree] at hlocalI
    omega
  have hcoeffJ : MvPolynomial.coeff
      (isotropicJLeadingExponent G.totalDegree eJ)
      (isotropicHomogenizedCircularChartJ G.totalDegree Q) ≠ 0 := by
    rw [inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicHomogenizedCircularChartJ_coeff_extremal
      G.totalDegree Q eJ hQdegree heJ heJmax]
    exact mul_ne_zero
      (mul_ne_zero (MvPolynomial.mem_support_iff.mp heJ)
        (pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero)))
      (pow_ne_zero _ (by norm_num))
  have hchartCoeffJ : MvPolynomial.coeff
      (isotropicJLeadingExponent G.totalDegree eJ)
      (projectiveCircularChart (-Complex.I)
        (planeHomogenization G.totalDegree G)) ≠ 0 := by
    change MvPolynomial.coeff (isotropicJLeadingExponent G.totalDegree eJ)
      (projectiveCircularChartJ (planeHomogenization G.totalDegree G)) ≠ 0
    rw [projectiveCircularChartJ_planeHomogenization_eq_isotropic]
    exact hcoeffJ
  have hlocalJ := inline_Esgk_MaximallyCircularIsotropicBidegree__planeCircularLocalOrder_le_degree_of_coeff_ne_zero
    (-Complex.I) hchartCoeffJ
  rw [inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicJLeadingExponent_degree G.totalDegree eJ heJdegree] at hlocalJ
  have horderJ : planeCircularLocalOrderJ G = p := by
    rcases hmax with ⟨hI, hJ⟩
    omega
  have heJbound : eJ 0 ≤ p := by
    have heJcoord : eJ 0 ≤ eJ.degree := by
      rw [inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add]
      omega
    change planeCircularLocalOrderJ G ≤ G.totalDegree - eJ 0 at hlocalJ
    rw [horderJ, hdegree] at hlocalJ
    omega
  change BidegreeBound p Q
  intro e he
  exact ⟨(heJmax e he).trans heJbound, (heImax e he).trans heIbound⟩

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

private theorem complex_I_ne_neg_I' : Complex.I ≠ -Complex.I := by
  intro h
  have him : (1 : ℝ) = -1 := congrArg Complex.im h
  have hlt : (-1 : ℝ) < 1 := lt_trans neg_one_lt_zero zero_lt_one
  exact (ne_of_gt hlt) him


theorem IsMaximallyCircular.rootMultiplicity_I_eq_localOrderI
    {G : PlanePoly} (hmax : IsMaximallyCircular G) (hG : G ≠ 0) :
    (complexPlaneInfinityRestriction G).rootMultiplicity Complex.I =
      planeCircularLocalOrderI G := by
  have hI : planeCircularLocalOrderI G ≤
      (complexPlaneInfinityRestriction G).rootMultiplicity Complex.I := by
    simpa [planeCircularLocalOrderI] using
      (planeCircularLocalOrder_le_rootMultiplicity Complex.I hG)
  have hJ : planeCircularLocalOrderJ G ≤
      (complexPlaneInfinityRestriction G).rootMultiplicity (-Complex.I) := by
    simpa [planeCircularLocalOrderJ] using
      (planeCircularLocalOrder_le_rootMultiplicity (-Complex.I) hG)
  have hroots :
      (complexPlaneInfinityRestriction G).rootMultiplicity Complex.I +
          (complexPlaneInfinityRestriction G).rootMultiplicity (-Complex.I) ≤ G.totalDegree :=
    (Polynomial.rootMultiplicity_add_rootMultiplicity_le_natDegree_of_ne
      (complexPlaneInfinityRestriction G) complex_I_ne_neg_I').trans
        (complexPlaneInfinityRestriction_natDegree_le G)
  have horders := hmax.order_sum_eq_totalDegree
  omega


theorem chartInfinityRestriction_homogeneousComponent_ne_zero_of_rootMultiplicity_eq
    (c : ℂ) {G : PlanePoly} (hG : G ≠ 0)
    (hsat : (complexPlaneInfinityRestriction G).rootMultiplicity c =
      planeCircularLocalOrder c G) :
    chartInfinityRestriction
        (MvPolynomial.homogeneousComponent (planeCircularLocalOrder c G)
          (projectiveCircularChart c (planeHomogenization G.totalDegree G))) ≠ 0 := by
  let m := planeCircularLocalOrder c G
  let F := projectiveCircularChart c (planeHomogenization G.totalDegree G)
  let q := (complexPlaneInfinityRestriction G).comp (Polynomial.X + Polynomial.C c)
  have hq : q ≠ 0 := by
    exact Polynomial.comp_X_add_C_ne_zero_iff.mpr
      (complexPlaneInfinityRestriction_ne_zero hG)
  have hqcoeff : q.coeff q.natTrailingDegree ≠ 0 :=
    Polynomial.coeff_natTrailingDegree_ne_zero.mpr hq
  have hdegree : q.natTrailingDegree = m := by
    calc
      q.natTrailingDegree =
          (complexPlaneInfinityRestriction G).rootMultiplicity c := by
        simpa [q] using
          (Polynomial.rootMultiplicity_eq_natTrailingDegree
            (p := complexPlaneInfinityRestriction G) (t := c)).symm
      _ = m := by simpa [m] using hsat
  have hrestrict : chartInfinityRestriction F = q := by
    exact chartInfinityRestriction_projectiveCircularChart_planeHomogenization c G
  have hcoeffF :
      MvPolynomial.coeff (Finsupp.cons m (0 : Fin 1 →₀ ℕ)) F ≠ 0 := by
    rw [← chartInfinityRestriction_coeff, hrestrict, ← hdegree]
    exact hqcoeff
  have hindexDegree :
      Finsupp.degree (Finsupp.cons m (0 : Fin 1 →₀ ℕ)) = m := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two, Finsupp.cons_zero]
    change m + (Finsupp.cons m (0 : Fin 1 →₀ ℕ)) (0 : Fin 1).succ = m
    rw [Finsupp.cons_succ]
    simp
  intro hzero
  apply hcoeffF
  have hcomponentCoeff :
      MvPolynomial.coeff (Finsupp.cons m (0 : Fin 1 →₀ ℕ))
          (MvPolynomial.homogeneousComponent m F) =
        MvPolynomial.coeff (Finsupp.cons m (0 : Fin 1 →₀ ℕ)) F := by
    simp [MvPolynomial.coeff_homogeneousComponent, hindexDegree]
  rw [← hcomponentCoeff, ← chartInfinityRestriction_coeff, hzero]
  simp


theorem IsMaximallyCircular.chartInfinityRestriction_tangentComponent_I_ne_zero
    {G : PlanePoly} (hmax : IsMaximallyCircular G) (hG : G ≠ 0) :
    chartInfinityRestriction
        (MvPolynomial.homogeneousComponent (planeCircularLocalOrderI G)
          (projectiveCircularChartI (planeHomogenization G.totalDegree G))) ≠ 0 := by
  exact chartInfinityRestriction_homogeneousComponent_ne_zero_of_rootMultiplicity_eq
    Complex.I hG (by
      simpa [planeCircularLocalOrderI] using hmax.rootMultiplicity_I_eq_localOrderI hG)


end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 as described in the repository LICENSE.
-/


namespace Esgk

open EuclideanGeometry


@[simp]
theorem xAxisReflectionAffineIsometry_apply (x : Point2) :
    xAxisReflectionAffineIsometry x = xAxisReflectionPoint x := rfl

@[simp]
theorem xAxisReflectionAffineIsometry_fixed_xAxisPoint (r : ℝ) :
    xAxisReflectionAffineIsometry (xAxisPoint r) = xAxisPoint r := by
  rw [xAxisReflectionAffineIsometry_apply]
  ext i
  fin_cases i
  · simp [xAxisReflectionPoint, xAxisPoint]
  · simp [xAxisReflectionPoint, xAxisPoint]

theorem affineIsometry_toRealAffineIsometry_linear_eq
    (g : Point2 ≃ᵃⁱ[ℝ] Point2) :
    g.toIsometryEquiv.toRealAffineIsometryEquiv.linearIsometryEquiv =
      g.linearIsometryEquiv := by
  apply LinearIsometryEquiv.ext
  intro y
  have h1 := g.toIsometryEquiv.toRealAffineIsometryEquiv.map_vsub (y + 0) 0
  have h2 := g.map_vsub (y + 0) 0
  rw [IsometryEquiv.coeFn_toRealAffineIsometryEquiv] at h1
  have hxa : (g.toIsometryEquiv : Point2 → Point2) = (g : Point2 → Point2) := rfl
  rw [hxa] at h1
  have hy : (y + 0) -ᵥ (0 : Point2) = y := by simp
  rw [hy] at h1 h2
  exact h1.trans h2.symm

theorem xAxisReflectionAffineIsometry_not_isDirect :
    ¬ IsDirect xAxisReflectionAffineIsometry.toIsometryEquiv := by
  have hlin := affineIsometry_toRealAffineIsometry_linear_eq
    xAxisReflectionAffineIsometry
  have hmatrix :
      LinearMap.toMatrix
          ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis)
          ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis)
          (xAxisReflectionLinearIsometry.toLinearEquiv : Point2 →ₗ[ℝ] Point2) =
        !![1, 0; 0, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, xAxisReflectionLinearIsometry,
        xAxisReflectionLinear, xAxisReflectionPoint,
        EuclideanSpace.basisFun_apply]
  intro hdirect
  change 0 < LinearMap.det
    (xAxisReflectionAffineIsometry.toIsometryEquiv.toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearEquiv :
      Point2 →ₗ[ℝ] Point2) at hdirect
  rw [hlin, ← LinearMap.det_toMatrix
    ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis)] at hdirect
  rw [show xAxisReflectionAffineIsometry.linearIsometryEquiv =
    xAxisReflectionLinearIsometry by rfl, hmatrix] at hdirect
  norm_num [Matrix.det_fin_two_of] at hdirect

theorem xAxisReflectionAffineIsometry_not_isDirect_conjugate
    (g : Point2 ≃ᵃⁱ[ℝ] Point2) :
    ¬ IsDirect
      ((g.trans xAxisReflectionAffineIsometry).trans g.symm).toIsometryEquiv := by
  let ρ := xAxisReflectionAffineIsometry
  let h := (g.trans ρ).trans g.symm
  have hlin (q : Point2 ≃ᵃⁱ[ℝ] Point2) :
      q.toIsometryEquiv.toRealAffineIsometryEquiv.linearIsometryEquiv =
        q.linearIsometryEquiv :=
    affineIsometry_toRealAffineIsometry_linear_eq q
  let det (q : Point2 ≃ᵃⁱ[ℝ] Point2) : ℝ :=
    LinearMap.det (q.linearIsometryEquiv.toLinearEquiv : Point2 →ₗ[ℝ] Point2)
  have hρne : det ρ ≠ 0 := by
    have hp := planeIsometryLinearPart_det_ne_zero ρ.toIsometryEquiv
    change LinearMap.det
      (ρ.toIsometryEquiv.toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearEquiv :
        Point2 →ₗ[ℝ] Point2) ≠ 0 at hp
    rw [hlin ρ] at hp
    exact hp
  have hρneg : det ρ < 0 := by
    have hρnonpos : det ρ ≤ 0 := by
      apply le_of_not_gt
      intro hρpos
      apply xAxisReflectionAffineIsometry_not_isDirect
      change 0 < LinearMap.det
        (ρ.toIsometryEquiv.toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearEquiv :
          Point2 →ₗ[ℝ] Point2)
      rw [hlin ρ]
      exact hρpos
    exact lt_of_le_of_ne hρnonpos hρne
  have hcomp (e₁ e₂ : Point2 ≃ᵃⁱ[ℝ] Point2) :
      (e₁.trans e₂).linearIsometryEquiv =
        e₁.linearIsometryEquiv.trans e₂.linearIsometryEquiv := by
    rfl
  have hdet_trans (e₁ e₂ : Point2 ≃ᵃⁱ[ℝ] Point2) :
      det (e₁.trans e₂) = det e₂ * det e₁ := by
    simp only [det, hcomp]
    have hmap :
        (((e₁.linearIsometryEquiv.trans e₂.linearIsometryEquiv).toLinearEquiv :
          Point2 →ₗ[ℝ] Point2)) =
          (e₂.linearIsometryEquiv.toLinearEquiv : Point2 →ₗ[ℝ] Point2) ∘ₗ
            (e₁.linearIsometryEquiv.toLinearEquiv : Point2 →ₗ[ℝ] Point2) := rfl
    rw [hmap, LinearMap.det_comp]
  have hprod : det g.symm * det g = 1 := by
    have hid : g.trans g.symm = AffineIsometryEquiv.refl ℝ Point2 :=
      AffineIsometryEquiv.self_trans_symm g
    have hdet := congrArg (fun q : Point2 ≃ᵃⁱ[ℝ] Point2 => det q) hid
    rw [hdet_trans] at hdet
    have hrefl : det (AffineIsometryEquiv.refl ℝ Point2) = 1 := by
      change LinearMap.det
        ((AffineIsometryEquiv.refl ℝ Point2).linearIsometryEquiv.toLinearEquiv :
          Point2 →ₗ[ℝ] Point2) = 1
      change LinearMap.det (LinearMap.id : Point2 →ₗ[ℝ] Point2) = 1
      rw [LinearMap.det_id]
    rw [hrefl] at hdet
    exact hdet
  intro hdirect
  change 0 < LinearMap.det
    (h.toIsometryEquiv.toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearEquiv :
      Point2 →ₗ[ℝ] Point2) at hdirect
  rw [hlin h] at hdirect
  change 0 < det h at hdirect
  rw [hdet_trans, hdet_trans] at hdirect
  have hdet : det g.symm * (det ρ * det g) = det ρ := by
    calc
      det g.symm * (det ρ * det g) = det ρ * (det g.symm * det g) := by ring
      _ = det ρ * 1 := by rw [hprod]
      _ = det ρ := by ring
  rw [hdet] at hdirect
  exact (not_lt_of_ge (le_of_lt hρneg)) hdirect

end Esgk

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open EuclideanGeometry PachDeZeeuw


@[simp]
theorem mem_selfCurveFixedAnchorsFor {d : ℕ}
    (X : PreparedBipartiteInput d) (g : Point2 ≃ᵢ Point2) (p : X.P₁) :
    p ∈ selfCurveFixedAnchorsFor X g ↔ g (p : Point2) = (p : Point2) := by
  classical
  simp [selfCurveFixedAnchorsFor]


@[simp]
theorem mem_selfCurveAxisAnchorsFromReflections {d : ℕ}
    (X : PreparedBipartiteInput d) (reflections : Finset (Point2 ≃ᵢ Point2))
    (p : X.P₁) :
    p ∈ selfCurveAxisAnchorsFromReflections X reflections ↔
      ∃ g ∈ reflections, g (p : Point2) = (p : Point2) := by
  classical
  simp [selfCurveAxisAnchorsFromReflections]

theorem selfCurveAxisAnchorsFromReflections_card_le {d : ℕ}
    (X : PreparedBipartiteInput d) (reflections : Finset (Point2 ≃ᵢ Point2))
    (hfixed : ∀ g ∈ reflections, (selfCurveFixedAnchorsFor X g).card ≤ d) :
    (selfCurveAxisAnchorsFromReflections X reflections).card ≤
      reflections.card * d := by
  classical
  calc
    (selfCurveAxisAnchorsFromReflections X reflections).card
        ≤ ∑ g ∈ reflections, (selfCurveFixedAnchorsFor X g).card := by
          simpa [selfCurveAxisAnchorsFromReflections] using
            (Finset.card_biUnion_le :
              (reflections.biUnion (selfCurveFixedAnchorsFor X)).card ≤
                ∑ g ∈ reflections, (selfCurveFixedAnchorsFor X g).card)
    _ ≤ ∑ _g ∈ reflections, d := by
      exact Finset.sum_le_sum fun g hg ↦ hfixed g hg
    _ = reflections.card * d := by simp

theorem selfCurveAxisAnchorsFromReflections_card_le_two_mul_degree_sq
    {d : ℕ} (X : PreparedBipartiteInput d)
    (reflections : Finset (Point2 ≃ᵢ Point2))
    (hreflections : reflections.card ≤ 2 * d)
    (hfixed : ∀ g ∈ reflections, (selfCurveFixedAnchorsFor X g).card ≤ d) :
    (selfCurveAxisAnchorsFromReflections X reflections).card ≤ 2 * d ^ 2 := by
  calc
    (selfCurveAxisAnchorsFromReflections X reflections).card
        ≤ reflections.card * d :=
      selfCurveAxisAnchorsFromReflections_card_le X reflections hfixed
    _ ≤ (2 * d) * d := Nat.mul_le_mul_right d hreflections
    _ = 2 * d ^ 2 := by ring


@[simp]
theorem mem_selfCurveSymmetryLabelsFor {d : ℕ}
    (X : PreparedBipartiteInput d) (g : Point2 ≃ᵢ Point2)
    (ij : X.P₁ × X.P₁) :
    ij ∈ selfCurveSymmetryLabelsFor X g ↔
      g (ij.1 : Point2) = (ij.2 : Point2) := by
  classical
  simp [selfCurveSymmetryLabelsFor]

theorem selfCurveSymmetryLabelsFor_card_le {d : ℕ}
    (X : PreparedBipartiteInput d) (g : Point2 ≃ᵢ Point2) :
    (selfCurveSymmetryLabelsFor X g).card ≤ X.P₁.card := by
  classical
  refine Finset.card_le_card_of_injOn (fun ij : X.P₁ × X.P₁ ↦ ij.1) ?_ ?_
  · intro ij hij
    simp
  · intro a ha b hb hfirst
    have haRel := (mem_selfCurveSymmetryLabelsFor X g a).1 ha
    have hbRel := (mem_selfCurveSymmetryLabelsFor X g b).1 hb
    have hfirstSubtype : a.1 = b.1 := Subtype.ext hfirst
    apply Prod.ext hfirstSubtype
    apply Subtype.ext
    calc
      (a.2 : Point2) = g (a.1 : Point2) := haRel.symm
      _ = g (b.1 : Point2) := by rw [hfirstSubtype]
      _ = (b.2 : Point2) := hbRel


@[simp]
theorem mem_selfCurveSymmetryLabels {d : ℕ}
    (X : PreparedBipartiteInput d) (symmetries : Finset (Point2 ≃ᵢ Point2))
    (ij : X.P₁ × X.P₁) :
    ij ∈ selfCurveSymmetryLabels X symmetries ↔
      ∃ g ∈ symmetries, g (ij.1 : Point2) = (ij.2 : Point2) := by
  classical
  simp [selfCurveSymmetryLabels]

theorem selfCurveSymmetryLabels_card_le {d : ℕ}
    (X : PreparedBipartiteInput d) (symmetries : Finset (Point2 ≃ᵢ Point2)) :
    (selfCurveSymmetryLabels X symmetries).card ≤
      symmetries.card * X.P₁.card := by
  classical
  calc
    (selfCurveSymmetryLabels X symmetries).card
        ≤ ∑ g ∈ symmetries, (selfCurveSymmetryLabelsFor X g).card := by
          simpa [selfCurveSymmetryLabels] using
            (Finset.card_biUnion_le :
              (symmetries.biUnion (selfCurveSymmetryLabelsFor X)).card ≤
                ∑ g ∈ symmetries, (selfCurveSymmetryLabelsFor X g).card)
    _ ≤ ∑ _g ∈ symmetries, X.P₁.card := by
      exact Finset.sum_le_sum fun g _hg ↦ selfCurveSymmetryLabelsFor_card_le X g
    _ = symmetries.card * X.P₁.card := by simp

theorem selfCurveSymmetryLabels_card_le_four_mul_degree_mul_card
    {d : ℕ} (X : PreparedBipartiteInput d)
    (symmetries : Finset (Point2 ≃ᵢ Point2))
    (hsymmetries : symmetries.card ≤ 4 * d) :
    (selfCurveSymmetryLabels X symmetries).card ≤ 4 * d * X.P₁.card := by
  calc
    (selfCurveSymmetryLabels X symmetries).card
        ≤ symmetries.card * X.P₁.card := selfCurveSymmetryLabels_card_le X symmetries
    _ ≤ (4 * d) * X.P₁.card := Nat.mul_le_mul_right X.P₁.card hsymmetries


end Esgk

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw PachDeZeeuw.Algebraic


private theorem inline_Esgk_SelfCurveSingularAnchorBound__selfCurveSingularAnchors_card_le_degree_mul_pred_of_partial
    {d : ℕ} (X : PreparedBipartiteInput d) (i : Fin 2)
    (hpartial : MvPolynomial.pderiv i (preparedSecondCurvePolynomial X) ≠ 0) :
    (selfCurveSingularAnchors X).card ≤
      (preparedSecondCurvePolynomial X).totalDegree *
        ((preparedSecondCurvePolynomial X).totalDegree - 1) := by
  classical
  let G : PlanePoly := preparedSecondCurvePolynomial X
  let embedding : X.P₁ ↪ (Fin 2 → ℝ) :=
    ⟨fun p j ↦ (p : PachDeZeeuw.Algebraic.Point2) j, by
      intro p q hpq
      apply Subtype.ext
      ext j
      exact congrFun hpq j⟩
  let S : Finset (Fin 2 → ℝ) := (selfCurveSingularAnchors X).map embedding
  have hS_card : S.card = (selfCurveSingularAnchors X).card := by
    simp [S]
  have hzero : ∀ z ∈ S,
      MvPolynomial.eval z G = 0 ∧
        MvPolynomial.eval z (MvPolynomial.pderiv i G) = 0 := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hz
    have hsing := (mem_selfCurveSingularAnchors X p).mp hp
    rw [SingularPointSet, Set.mem_inter_iff, Set.mem_inter_iff] at hsing
    rcases hsing with ⟨⟨hcurve, hzero0⟩, hzero1⟩
    have hcurve' : MvPolynomial.eval
        (fun j ↦ ((p : PachDeZeeuw.Algebraic.Point2) j)) G = 0 := by
      simpa [PlaneCurveZeroSet, G] using hcurve
    have hzero0' : MvPolynomial.eval
        (fun j ↦ ((p : PachDeZeeuw.Algebraic.Point2) j))
          (MvPolynomial.pderiv (0 : Fin 2) G) = 0 := by
      simpa [G] using hzero0
    have hzero1' : MvPolynomial.eval
        (fun j ↦ ((p : PachDeZeeuw.Algebraic.Point2) j))
          (MvPolynomial.pderiv (1 : Fin 2) G) = 0 := by
      simpa [G] using hzero1
    fin_cases i
    · exact ⟨hcurve', hzero0'⟩
    · exact ⟨hcurve', hzero1'⟩
  have hpos : 1 ≤ G.totalDegree := by
    simpa [G] using
      (one_le_totalDegree_of_pderiv_ne_zero
        (preparedSecondCurvePolynomial X) i hpartial)
  have hnot : ¬ G ∣ MvPolynomial.pderiv i G := by
    simpa [G] using
      (irreducible_not_dvd_nonzero_partial
        (preparedSecondCurvePolynomial X)
        (preparedSecondCurvePolynomial_irreducible X) hpartial)
  have hcount := sharp_finite_common_zero_count G
      (MvPolynomial.pderiv i G) S
      (by simpa [G] using preparedSecondCurvePolynomial_irreducible X)
      hpos hnot hzero
  have hdeg : (MvPolynomial.pderiv i G).totalDegree ≤ G.totalDegree - 1 := by
    exact totalDegree_pderiv_le_sub_one G i (Nat.zero_lt_of_lt hpos)
  have hbound : S.card ≤ G.totalDegree * (G.totalDegree - 1) := by
    exact le_trans hcount (Nat.mul_le_mul_left G.totalDegree hdeg)
  simpa [hS_card, G] using hbound


theorem selfCurveSingularAnchors_card_le_degree_mul_pred
    {d : ℕ} (X : PreparedBipartiteInput d) :
    (selfCurveSingularAnchors X).card ≤
      (preparedSecondCurvePolynomial X).totalDegree *
        ((preparedSecondCurvePolynomial X).totalDegree - 1) := by
  rcases irreducible_has_nonzero_partial
      (preparedSecondCurvePolynomial X)
      (preparedSecondCurvePolynomial_irreducible X) with hpartial | hpartial
  · exact inline_Esgk_SelfCurveSingularAnchorBound__selfCurveSingularAnchors_card_le_degree_mul_pred_of_partial X 0 hpartial
  · exact inline_Esgk_SelfCurveSingularAnchorBound__selfCurveSingularAnchors_card_le_degree_mul_pred_of_partial X 1 hpartial


theorem selfCurveSingularAnchors_card_le_degree_mul_pred_degree
    {d : ℕ} (X : PreparedBipartiteInput d) :
    (selfCurveSingularAnchors X).card ≤ d * (d - 1) := by
  calc
    (selfCurveSingularAnchors X).card ≤
        (preparedSecondCurvePolynomial X).totalDegree *
          ((preparedSecondCurvePolynomial X).totalDegree - 1) :=
      selfCurveSingularAnchors_card_le_degree_mul_pred X
    _ ≤ d * (d - 1) := by
      have hdegree := preparedSecondCurvePolynomial_totalDegree_le X
      exact Nat.mul_le_mul hdegree (Nat.sub_le_sub_right hdegree 1)

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic


theorem circularChartDehomogenization_eq_map_finSuccEquiv (T : CircularChartPoly) :
    circularChartDehomogenization T =
      Polynomial.map (MvPolynomial.eval (fun _ : Fin 1 ↦ (1 : ℂ)))
        (MvPolynomial.finSuccEquiv ℂ 1 T) := by
  let φ : CircularChartPoly →+* Polynomial ℂ :=
    (Polynomial.mapRingHom
      (MvPolynomial.eval (fun _ : Fin 1 ↦ (1 : ℂ)))).comp
      (MvPolynomial.finSuccEquiv ℂ 1).toRingEquiv.toRingHom
  change circularChartDehomogenization T = φ T
  congr 1
  dsimp [φ]
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [RingHom.comp_apply, circularChartDehomogenization,
      MvPolynomial.finSuccEquiv_apply]
  · intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    ·
      simp [RingHom.comp_apply, circularChartDehomogenization,
        MvPolynomial.finSuccEquiv_apply]
    ·
      simp [RingHom.comp_apply, circularChartDehomogenization,
        MvPolynomial.finSuccEquiv_apply]

 
theorem circularChartDehomogenization_natDegree_le {T : CircularChartPoly} {p : ℕ}
    (hT : MvPolynomial.IsHomogeneous T p) :
    (circularChartDehomogenization T).natDegree ≤ p := by
  rw [circularChartDehomogenization_eq_map_finSuccEquiv]
  calc
    (Polynomial.map (MvPolynomial.eval (fun _ : Fin 1 ↦ (1 : ℂ)))
          (MvPolynomial.finSuccEquiv ℂ 1 T)).natDegree ≤
        (MvPolynomial.finSuccEquiv ℂ 1 T).natDegree := Polynomial.natDegree_map_le
    _ = T.degreeOf 0 := MvPolynomial.natDegree_finSuccEquiv T
    _ ≤ T.totalDegree := MvPolynomial.degreeOf_le_totalDegree T 0
    _ ≤ p := hT.totalDegree_le


theorem circularChartDehomogenization_coeff_eq_chartInfinityRestriction_coeff
    {T : CircularChartPoly} {p : ℕ} (hT : MvPolynomial.IsHomogeneous T p) :
    (circularChartDehomogenization T).coeff p = (chartInfinityRestriction T).coeff p := by
  have hhomogenize : (circularChartDehomogenization T).homogenize p = T := by
    apply Polynomial.homogenize_eq_of_isHomogeneous hT
    rfl
  let d : Fin 2 →₀ ℕ := Finsupp.cons p (0 : Fin 1 →₀ ℕ)
  calc
    (circularChartDehomogenization T).coeff p =
        MvPolynomial.coeff d ((circularChartDehomogenization T).homogenize p) := by
      rw [Polynomial.coeff_homogenize]
      have hd0 : d 0 = p := by simp [d, Finsupp.cons_zero]
      have hd1 : d 1 = 0 := by
        change (Finsupp.cons p (0 : Fin 1 →₀ ℕ)) (Fin.succ 0) = 0
        exact Finsupp.cons_succ (0 : Fin 1) p (0 : Fin 1 →₀ ℕ)
      simp [hd0, hd1]
    _ = MvPolynomial.coeff d T := by rw [hhomogenize]
    _ = (chartInfinityRestriction T).coeff p := by
      rw [chartInfinityRestriction_coeff]

private theorem inline_Esgk_CircularTangentDehomogenization__chartInfinityRestriction_coeff_ne_zero_of_isHomogeneous
    {T : CircularChartPoly} {p : ℕ} (hT : MvPolynomial.IsHomogeneous T p)
    (hrestriction : chartInfinityRestriction T ≠ 0) :
    (chartInfinityRestriction T).coeff p ≠ 0 := by
  intro hp
  apply hrestriction
  ext k
  by_cases hkp : k = p
  · simpa [hkp] using hp
  · rw [chartInfinityRestriction_coeff]
    apply hT.coeff_eq_zero
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two, Finsupp.cons_zero]
    change k + (Finsupp.cons k (0 : Fin 1 →₀ ℕ)) (Fin.succ 0) ≠ p
    rw [Finsupp.cons_succ, Finsupp.zero_apply, add_zero]
    exact hkp


theorem circularChartDehomogenization_ne_zero_of_isHomogeneous
    {T : CircularChartPoly} {p : ℕ} (hT : MvPolynomial.IsHomogeneous T p)
    (hrestriction : chartInfinityRestriction T ≠ 0) :
    circularChartDehomogenization T ≠ 0 := by
  intro hzero
  have hcoeff := inline_Esgk_CircularTangentDehomogenization__chartInfinityRestriction_coeff_ne_zero_of_isHomogeneous hT hrestriction
  apply hcoeff
  rw [← circularChartDehomogenization_coeff_eq_chartInfinityRestriction_coeff hT, hzero]
  simp


theorem circularChartDehomogenization_natDegree_eq_of_isHomogeneous
    {T : CircularChartPoly} {p : ℕ} (hT : MvPolynomial.IsHomogeneous T p)
    (hrestriction : chartInfinityRestriction T ≠ 0) :
    (circularChartDehomogenization T).natDegree = p := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (circularChartDehomogenization_natDegree_le hT)
  rw [circularChartDehomogenization_coeff_eq_chartInfinityRestriction_coeff hT]
  exact inline_Esgk_CircularTangentDehomogenization__chartInfinityRestriction_coeff_ne_zero_of_isHomogeneous hT hrestriction


theorem IsMaximallyCircular.circularChartDehomogenization_tangentComponent_I_ne_zero
    {G : PlanePoly} (hmax : IsMaximallyCircular G) (hG : G ≠ 0) :
    circularChartDehomogenization
        (MvPolynomial.homogeneousComponent (planeCircularLocalOrderI G)
          (projectiveCircularChartI (planeHomogenization G.totalDegree G))) ≠ 0 := by
  exact circularChartDehomogenization_ne_zero_of_isHomogeneous
    (T := MvPolynomial.homogeneousComponent (planeCircularLocalOrderI G)
      (projectiveCircularChartI (planeHomogenization G.totalDegree G)))
    (p := planeCircularLocalOrderI G)
    (MvPolynomial.homogeneousComponent_isHomogeneous
      (n := planeCircularLocalOrderI G)
      (φ := projectiveCircularChartI (planeHomogenization G.totalDegree G)))
    (hmax.chartInfinityRestriction_tangentComponent_I_ne_zero hG)


theorem IsMaximallyCircular.circularChartDehomogenization_tangentComponent_I_natDegree
    {G : PlanePoly} (hmax : IsMaximallyCircular G) (hG : G ≠ 0) :
    (circularChartDehomogenization
      (MvPolynomial.homogeneousComponent (planeCircularLocalOrderI G)
        (projectiveCircularChartI
          (planeHomogenization G.totalDegree G)))).natDegree = planeCircularLocalOrderI G := by
  exact circularChartDehomogenization_natDegree_eq_of_isHomogeneous
    (T := MvPolynomial.homogeneousComponent (planeCircularLocalOrderI G)
      (projectiveCircularChartI (planeHomogenization G.totalDegree G)))
    (p := planeCircularLocalOrderI G)
    (MvPolynomial.homogeneousComponent_isHomogeneous
      (n := planeCircularLocalOrderI G)
      (φ := projectiveCircularChartI (planeHomogenization G.totalDegree G)))
    (hmax.chartInfinityRestriction_tangentComponent_I_ne_zero hG)

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

namespace IrreduciblePlanePolynomial


@[simp]
theorem coordinateRingEval_coordinateClass
    (C : IrreduciblePlanePolynomial ℝ) (a : PachDeZeeuw.Algebraic.Point2)
    (ha : a ∈ PlaneCurveZeroSet C.polynomial) (i : Fin 2) :
    C.coordinateRingEval a ha (C.coordinateClass i) = a i := by
  set_option backward.isDefEq.respectTransparency false in
    simp [coordinateRingEval, coordinateClass]


@[simp]
theorem mem_coordinateRingEvalSubmonoid
    (C : IrreduciblePlanePolynomial ℝ) (a : PachDeZeeuw.Algebraic.Point2)
    (ha : a ∈ PlaneCurveZeroSet C.polynomial) (z : C.CoordinateRing) :
    z ∈ C.coordinateRingEvalSubmonoid a ha ↔
      z ∉ RingHom.ker (C.coordinateRingEval a ha).toRingHom := by
  change IsUnit (C.coordinateRingEval a ha z) ↔
    C.coordinateRingEval a ha z ≠ 0
  exact isUnit_iff_ne_zero


theorem coordinateRingEvalIdeal_eq_coordinateDifferenceIdeal
    (C : IrreduciblePlanePolynomial ℝ) (a : PachDeZeeuw.Algebraic.Point2)
    (ha : a ∈ PlaneCurveZeroSet C.polynomial) :
    C.coordinateRingEvalIdeal a ha = C.coordinateDifferenceIdeal a := by
  apply le_antisymm
  · intro z hz
    have hzTop : z ∈ Algebra.adjoin ℝ (Set.range C.coordinateClass) := by
      rw [C.adjoin_coordinateClass_range_eq_top]
      simp
    have hdiff :
        z - algebraMap ℝ C.CoordinateRing (C.coordinateRingEval a ha z) ∈
          C.coordinateDifferenceIdeal a := by
      refine Algebra.adjoin_induction (s := Set.range C.coordinateClass)
        (p := fun z _ ↦
          z - algebraMap ℝ C.CoordinateRing (C.coordinateRingEval a ha z) ∈
            C.coordinateDifferenceIdeal a) ?_ ?_ ?_ ?_ hzTop
      · rintro _ ⟨i, rfl⟩
        rw [C.coordinateRingEval_coordinateClass a ha i]
        change C.coordinateDifferenceAt a i ∈ C.coordinateDifferenceIdeal a
        exact Ideal.subset_span (Set.mem_range_self i)
      · intro r
        simp
      · intro x y _hx _hy hxmem hymem
        convert (C.coordinateDifferenceIdeal a).add_mem hxmem hymem using 1
        simp only [map_add]
        ring
      · intro x y _hx _hy hxmem hymem
        have hleft := (C.coordinateDifferenceIdeal a).mul_mem_left x hymem
        have hright := (C.coordinateDifferenceIdeal a).mul_mem_right
          (algebraMap ℝ C.CoordinateRing (C.coordinateRingEval a ha y)) hxmem
        convert (C.coordinateDifferenceIdeal a).add_mem hleft hright using 1
        simp only [map_mul]
        ring
    have hz0 : C.coordinateRingEval a ha z = 0 := RingHom.mem_ker.mp hz
    simpa [hz0] using hdiff
  · rw [coordinateDifferenceIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change C.coordinateRingEval a ha (C.coordinateDifferenceAt a i) = 0
    simp [coordinateDifferenceAt]


theorem coordinateRingEvalSubmonoid_eq_primeCompl
    (C : IrreduciblePlanePolynomial ℝ) (a : PachDeZeeuw.Algebraic.Point2)
    (ha : a ∈ PlaneCurveZeroSet C.polynomial) :
    C.coordinateRingEvalSubmonoid a ha =
      (C.coordinateRingEvalIdeal a ha).primeCompl := by
  ext z
  simpa only [coordinateRingEvalIdeal, Ideal.mem_primeCompl_iff] using
    C.mem_coordinateRingEvalSubmonoid a ha z


theorem map_coordinateRingEvalIdeal_eq_span_coordinateDifferences
    (C : IrreduciblePlanePolynomial ℝ) (a : PachDeZeeuw.Algebraic.Point2)
    (ha : a ∈ PlaneCurveZeroSet C.polynomial) :
    Ideal.map
        (algebraMap C.CoordinateRing
          (Localization (C.coordinateRingEvalSubmonoid a ha)))
        (C.coordinateRingEvalIdeal a ha) =
      Ideal.span
        (Set.range (fun i ↦
          algebraMap C.CoordinateRing
            (Localization (C.coordinateRingEvalSubmonoid a ha))
            (C.coordinateDifferenceAt a i))) := by
  rw [C.coordinateRingEvalIdeal_eq_coordinateDifferenceIdeal,
    coordinateDifferenceIdeal, Ideal.map_span]
  congr 1
  ext z
  simp


theorem map_coordinateRingEvalIdeal_isPrincipal_of_coordinateDifferences_mem
    (C : IrreduciblePlanePolynomial ℝ) (a : PachDeZeeuw.Algebraic.Point2)
    (ha : a ∈ PlaneCurveZeroSet C.polynomial) (i : Fin 2)
    (hgen : ∀ j,
      algebraMap C.CoordinateRing
          (Localization (C.coordinateRingEvalSubmonoid a ha))
          (C.coordinateDifferenceAt a j) ∈
        Ideal.span ({algebraMap C.CoordinateRing
          (Localization (C.coordinateRingEvalSubmonoid a ha))
          (C.coordinateDifferenceAt a i)} : Set _)) :
    (Ideal.map
      (algebraMap C.CoordinateRing
        (Localization (C.coordinateRingEvalSubmonoid a ha)))
      (C.coordinateRingEvalIdeal a ha)).IsPrincipal := by
  rw [C.map_coordinateRingEvalIdeal_eq_span_coordinateDifferences]
  let g := algebraMap C.CoordinateRing
    (Localization (C.coordinateRingEvalSubmonoid a ha))
    (C.coordinateDifferenceAt a i)
  refine ⟨g, ?_⟩
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact hgen j
  · rw [Ideal.span_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact Ideal.subset_span (Set.mem_range_self i)


@[simp]
theorem basePoint_realAffineNormalizationPointOfAtPrimeRetraction
    (C : IrreduciblePlanePolynomial ℝ) (a : PachDeZeeuw.Algebraic.Point2)
    (ha : a ∈ PlaneCurveZeroSet C.polynomial)
    (retract : C.affineNormalizationRing →ₐ[C.CoordinateRing]
      Localization (C.coordinateRingEvalSubmonoid a ha)) :
    (C.realAffineNormalizationPointOfAtPrimeRetraction a ha retract).basePoint = a := by
  ext i
  change C.coordinateRingAtPointEval a ha
      (retract (algebraMap C.CoordinateRing C.affineNormalizationRing
        (C.coordinateClass i))) = a i
  rw [retract.commutes, C.coordinateRingAtPointEval_algebraMap]
  exact C.coordinateRingEval_coordinateClass a ha i

 
theorem exists_realAffineNormalizationPoint_basePoint_eq_of_atPrimeRetraction
    (C : IrreduciblePlanePolynomial ℝ) (a : PachDeZeeuw.Algebraic.Point2)
    (ha : a ∈ PlaneCurveZeroSet C.polynomial)
    (retract : C.affineNormalizationRing →ₐ[C.CoordinateRing]
      Localization (C.coordinateRingEvalSubmonoid a ha)) :
    ∃ x : C.RealAffineNormalizationPoint, x.basePoint = a :=
  ⟨C.realAffineNormalizationPointOfAtPrimeRetraction a ha retract,
    C.basePoint_realAffineNormalizationPointOfAtPrimeRetraction a ha retract⟩


theorem exists_realAffineNormalizationPoint_basePoint_eq_of_integrallyClosed_evalLocalization
    (C : IrreduciblePlanePolynomial ℝ) (a : PachDeZeeuw.Algebraic.Point2)
    (ha : a ∈ PlaneCurveZeroSet C.polynomial)
    (hnormal : IsIntegrallyClosed
      (Localization (C.coordinateRingEvalSubmonoid a ha))) :
    ∃ x : C.RealAffineNormalizationPoint, x.basePoint = a := by
  let A := C.CoordinateRing
  let S := C.coordinateRingEvalSubmonoid a ha
  let L := Localization S
  let K := C.FunctionField
  letI : IsIntegrallyClosed L := hnormal
  have hS : S ≤ nonZeroDivisors A := by
    intro z hz
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro hz0
    subst z
    change IsUnit ((C.coordinateRingEval a ha) 0) at hz
    rw [map_zero] at hz
    exact not_isUnit_zero hz
  let g : L →+* K :=
    IsLocalization.map (R := A) (S := L) (M := S) (P := A)
      K (T := nonZeroDivisors A) (RingHom.id A) hS
  letI : Algebra L K := g.toAlgebra
  letI : IsScalarTower A L K := IsScalarTower.of_algebraMap_eq' <| by
    change algebraMap A K = g.comp (algebraMap A L)
    symm
    simpa only [RingHom.comp_id] using
      (IsLocalization.map_comp (S := L) (Q := K)
        (g := RingHom.id A) hS)
  letI : IsFractionRing L K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization S L K
  let promote : C.affineNormalizationRing →+* integralClosure L K :=
    { toFun := fun z ↦ ⟨z.1, z.2.tower_top⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  let back : integralClosure L K ≃ₐ[L] L :=
    (Subalgebra.equivOfEq _ _
      (IsIntegrallyClosed.integralClosure_eq_bot L K)).trans
      (Algebra.botEquivOfInjective (IsFractionRing.injective L K))
  have hg : Function.Injective g := by
    change Function.Injective (algebraMap L K)
    exact IsFractionRing.injective L K
  have hback (z : integralClosure L K) :
      g (back z) = z.1 := by
    conv_rhs => rw [← back.symm_apply_apply z]
    rfl
  let retract : C.affineNormalizationRing →ₐ[C.CoordinateRing] L :=
    { toRingHom := back.toRingHom.comp promote
      commutes' := fun r ↦ by
        apply hg
        change g (back (promote
          (algebraMap C.CoordinateRing C.affineNormalizationRing r))) =
            g (algebraMap C.CoordinateRing L r)
        rw [hback (promote
          (algebraMap C.CoordinateRing C.affineNormalizationRing r))]
        exact IsScalarTower.algebraMap_apply C.CoordinateRing L K r }
  exact C.exists_realAffineNormalizationPoint_basePoint_eq_of_atPrimeRetraction
    a ha retract


theorem isIntegrallyClosed_evalLocalization_of_map_evalIdeal_isPrincipal
    (C : IrreduciblePlanePolynomial ℝ) (a : PachDeZeeuw.Algebraic.Point2)
    (ha : a ∈ PlaneCurveZeroSet C.polynomial)
    (hprincipal :
      (Ideal.map
        (algebraMap C.CoordinateRing
          (Localization (C.coordinateRingEvalSubmonoid a ha)))
        (C.coordinateRingEvalIdeal a ha)).IsPrincipal) :
    IsIntegrallyClosed
      (Localization (C.coordinateRingEvalSubmonoid a ha)) := by
  rw [C.coordinateRingEvalSubmonoid_eq_primeCompl] at hprincipal ⊢
  have hmax :
      (IsLocalRing.maximalIdeal
        (Localization (C.coordinateRingEvalIdeal a ha).primeCompl)).IsPrincipal := by
    simpa only [Localization.AtPrime.map_eq_maximalIdeal] using hprincipal
  have hnormal :
      IsIntegrallyClosed
          (Localization (C.coordinateRingEvalIdeal a ha).primeCompl) ∧
        ∀ P : Ideal (Localization (C.coordinateRingEvalIdeal a ha).primeCompl),
          P ≠ ⊥ → P.IsPrime →
            P = IsLocalRing.maximalIdeal
              (Localization (C.coordinateRingEvalIdeal a ha).primeCompl) :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
      (Localization (C.coordinateRingEvalIdeal a ha).primeCompl)).out 4 3).mp hmax
  exact hnormal.1


theorem exists_point_and_comap_basePoint_eq_and_dist_eq_of_infinite_intersection_of_integrallyClosed
    (C : IrreduciblePlanePolynomial ℝ)
    (g₁ g₂ : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) {r₁ r₂ : ℝ}
    (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0)
    (hns₁ :
      xAxisReflectionPoint ''
          PlaneCurveZeroSet (C.affineIsometryTransport g₁).polynomial ≠
        PlaneCurveZeroSet (C.affineIsometryTransport g₁).polynomial)
    (hns₂ :
      xAxisReflectionPoint ''
          PlaneCurveZeroSet (C.affineIsometryTransport g₂).polynomial ≠
        PlaneCurveZeroSet (C.affineIsometryTransport g₂).polynomial)
    (a c b d : PachDeZeeuw.Algebraic.Point2)
    (hg₁a : g₁ a = xAxisPoint (-r₁))
    (hg₁c : g₁ c = xAxisPoint r₁)
    (hg₂b : g₂ b = xAxisPoint (-r₂))
    (hg₂d : g₂ d = xAxisPoint r₂)
    (hinf : (twoPairDistanceCommonZeroSet C a c b d).Infinite)
    (ha : a ∈ PlaneCurveZeroSet C.polynomial)
    (hnormal : IsIntegrallyClosed
      (Localization (C.coordinateRingEvalSubmonoid a ha))) :
    ∃ x : C.RealAffineNormalizationPoint,
      ∃ degreeRight : C.affineNormalizationRing ≃ₐ[ℝ] C.affineNormalizationRing,
        x.basePoint = a ∧ (x.comap degreeRight).basePoint = b ∧ dist a c = dist b d := by
  obtain ⟨x, hxa⟩ :=
    C.exists_realAffineNormalizationPoint_basePoint_eq_of_integrallyClosed_evalLocalization
      a ha hnormal
  obtain ⟨degreeRight, hxb, hdist⟩ :=
    RealAffineNormalizationPoint.exists_comap_basePoint_eq_and_dist_eq_of_infinite_intersection
      C g₁ g₂ hr₁ hr₂ hns₁ hns₂ a c b d hg₁a hg₁c hg₂b hg₂d hinf x hxa
  exact ⟨x, degreeRight, hxa, hxb, hdist⟩


theorem exists_point_and_comap_basePoint_eq_and_dist_eq_of_infinite_intersection_of_principal_evalIdeal
    (C : IrreduciblePlanePolynomial ℝ)
    (g₁ g₂ : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) {r₁ r₂ : ℝ}
    (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0)
    (hns₁ :
      xAxisReflectionPoint ''
          PlaneCurveZeroSet (C.affineIsometryTransport g₁).polynomial ≠
        PlaneCurveZeroSet (C.affineIsometryTransport g₁).polynomial)
    (hns₂ :
      xAxisReflectionPoint ''
          PlaneCurveZeroSet (C.affineIsometryTransport g₂).polynomial ≠
        PlaneCurveZeroSet (C.affineIsometryTransport g₂).polynomial)
    (a c b d : PachDeZeeuw.Algebraic.Point2)
    (hg₁a : g₁ a = xAxisPoint (-r₁))
    (hg₁c : g₁ c = xAxisPoint r₁)
    (hg₂b : g₂ b = xAxisPoint (-r₂))
    (hg₂d : g₂ d = xAxisPoint r₂)
    (hinf : (twoPairDistanceCommonZeroSet C a c b d).Infinite)
    (ha : a ∈ PlaneCurveZeroSet C.polynomial)
    (hprincipal :
      (Ideal.map
        (algebraMap C.CoordinateRing
          (Localization (C.coordinateRingEvalSubmonoid a ha)))
        (C.coordinateRingEvalIdeal a ha)).IsPrincipal) :
    ∃ x : C.RealAffineNormalizationPoint,
      ∃ degreeRight : C.affineNormalizationRing ≃ₐ[ℝ] C.affineNormalizationRing,
        x.basePoint = a ∧ (x.comap degreeRight).basePoint = b ∧ dist a c = dist b d := by
  apply
    C.exists_point_and_comap_basePoint_eq_and_dist_eq_of_infinite_intersection_of_integrallyClosed
      g₁ g₂ hr₁ hr₂ hns₁ hns₂ a c b d hg₁a hg₁c hg₂b hg₂d hinf ha
  exact C.isIntegrallyClosed_evalLocalization_of_map_evalIdeal_isPrincipal
    a ha hprincipal


theorem exists_point_and_comap_basePoint_eq_and_dist_eq_of_infinite_intersection_of_coordinateDifference_generator
    (C : IrreduciblePlanePolynomial ℝ)
    (g₁ g₂ : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) {r₁ r₂ : ℝ}
    (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0)
    (hns₁ :
      xAxisReflectionPoint ''
          PlaneCurveZeroSet (C.affineIsometryTransport g₁).polynomial ≠
        PlaneCurveZeroSet (C.affineIsometryTransport g₁).polynomial)
    (hns₂ :
      xAxisReflectionPoint ''
          PlaneCurveZeroSet (C.affineIsometryTransport g₂).polynomial ≠
        PlaneCurveZeroSet (C.affineIsometryTransport g₂).polynomial)
    (a c b d : PachDeZeeuw.Algebraic.Point2)
    (hg₁a : g₁ a = xAxisPoint (-r₁))
    (hg₁c : g₁ c = xAxisPoint r₁)
    (hg₂b : g₂ b = xAxisPoint (-r₂))
    (hg₂d : g₂ d = xAxisPoint r₂)
    (hinf : (twoPairDistanceCommonZeroSet C a c b d).Infinite)
    (ha : a ∈ PlaneCurveZeroSet C.polynomial)
    (i : Fin 2)
    (hgen : ∀ j,
      algebraMap C.CoordinateRing
          (Localization (C.coordinateRingEvalSubmonoid a ha))
          (C.coordinateDifferenceAt a j) ∈
        Ideal.span ({algebraMap C.CoordinateRing
          (Localization (C.coordinateRingEvalSubmonoid a ha))
          (C.coordinateDifferenceAt a i)} : Set _)) :
    ∃ x : C.RealAffineNormalizationPoint,
      ∃ degreeRight : C.affineNormalizationRing ≃ₐ[ℝ] C.affineNormalizationRing,
        x.basePoint = a ∧ (x.comap degreeRight).basePoint = b ∧ dist a c = dist b d := by
  apply
    C.exists_point_and_comap_basePoint_eq_and_dist_eq_of_infinite_intersection_of_principal_evalIdeal
      g₁ g₂ hr₁ hr₂ hns₁ hns₂ a c b d hg₁a hg₁c hg₂b hg₂d hinf ha
  exact C.map_coordinateRingEvalIdeal_isPrincipal_of_coordinateDifferences_mem
    a ha i hgen


end IrreduciblePlanePolynomial

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

variable {n : ℕ}


theorem IsMaximallyCircular.circularITangentPolynomial_ne_zero
    {G : PlanePoly} (hmax : IsMaximallyCircular G) (hG : G ≠ 0) :
    circularITangentPolynomial G ≠ 0 := by
  exact hmax.circularChartDehomogenization_tangentComponent_I_ne_zero hG


theorem IsMaximallyCircular.circularITangentPolynomial_natDegree
    {G : PlanePoly} {pdeg : ℕ} (hmax : IsMaximallyCircular G) (hG : G ≠ 0)
    (hdegree : G.totalDegree = 2 * pdeg) :
    (circularITangentPolynomial G).natDegree = pdeg := by
  have hI := hmax.1
  have hlocal : planeCircularLocalOrderI G = pdeg := by
    omega
  rw [circularITangentPolynomial,
    hmax.circularChartDehomogenization_tangentComponent_I_natDegree hG, hlocal]


end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

namespace IrreduciblePlanePolynomial


theorem localization_left_mem_span_right_of_relation
    {A : Type*} [CommRing A] (S : Submonoid A) (x y q r : A)
    (hrel : x * q + y * r = 0) (hq : q ∈ S) :
    algebraMap A (Localization S) x ∈
      Ideal.span ({algebraMap A (Localization S) y} : Set _) := by
  let L := Localization S
  let x' : L := algebraMap A L x
  let y' : L := algebraMap A L y
  let q' : L := algebraMap A L q
  let r' : L := algebraMap A L r
  have hunit : IsUnit q' := IsLocalization.map_units L ⟨q, hq⟩
  have hmap₀ := congrArg (algebraMap A L) hrel
  have hmap : x' * q' + y' * r' = 0 := by
    calc
      x' * q' + y' * r' = algebraMap A L (x * q + y * r) := by
        rw [(algebraMap A L).map_add, (algebraMap A L).map_mul,
          (algebraMap A L).map_mul]
      _ = algebraMap A L 0 := hmap₀
      _ = 0 := (algebraMap A L).map_zero
  obtain ⟨qinv, hqinv, _⟩ := isUnit_iff_exists.mp hunit
  let I : Ideal L := Ideal.span ({y'} : Set L)
  change x' ∈ I
  have heq : x' * q' = -(y' * r') := eq_neg_of_add_eq_zero_left hmap
  have hcoeff : (-r' * qinv) * y' = x' := by
    calc
      (-r' * qinv) * y' = (-(y' * r')) * qinv := by ring
      _ = (x' * q') * qinv := by rw [← heq]
      _ = x' := by rw [mul_assoc, hqinv, mul_one]
  rw [← hcoeff]
  exact I.mul_mem_left (-r' * qinv) (Ideal.mem_span_singleton_self y')


theorem coordinateDifferences_mem_span_one_of_relation_of_leftCoefficient_ne_zero
    (C : IrreduciblePlanePolynomial ℝ) (a : PachDeZeeuw.Algebraic.Point2)
    (ha : a ∈ PlaneCurveZeroSet C.polynomial) (q₀ q₁ : C.CoordinateRing)
    (hrel :
      C.coordinateDifferenceAt a 0 * q₀ +
          C.coordinateDifferenceAt a 1 * q₁ = 0)
    (hq₀ : C.coordinateRingEval a ha q₀ ≠ 0) :
    ∀ j,
      algebraMap C.CoordinateRing
          (Localization (C.coordinateRingEvalSubmonoid a ha))
          (C.coordinateDifferenceAt a j) ∈
        Ideal.span ({algebraMap C.CoordinateRing
          (Localization (C.coordinateRingEvalSubmonoid a ha))
          (C.coordinateDifferenceAt a 1)} : Set _) := by
  intro j
  fin_cases j
  · apply localization_left_mem_span_right_of_relation
      (C.coordinateRingEvalSubmonoid a ha)
      (C.coordinateDifferenceAt a 0) (C.coordinateDifferenceAt a 1) q₀ q₁ hrel
    rw [C.mem_coordinateRingEvalSubmonoid]
    exact fun hker ↦ hq₀ (RingHom.mem_ker.mp hker)
  · exact Ideal.mem_span_singleton_self _


theorem coordinateDifferences_mem_span_zero_of_relation_of_rightCoefficient_ne_zero
    (C : IrreduciblePlanePolynomial ℝ) (a : PachDeZeeuw.Algebraic.Point2)
    (ha : a ∈ PlaneCurveZeroSet C.polynomial) (q₀ q₁ : C.CoordinateRing)
    (hrel :
      C.coordinateDifferenceAt a 0 * q₀ +
          C.coordinateDifferenceAt a 1 * q₁ = 0)
    (hq₁ : C.coordinateRingEval a ha q₁ ≠ 0) :
    ∀ j,
      algebraMap C.CoordinateRing
          (Localization (C.coordinateRingEvalSubmonoid a ha))
          (C.coordinateDifferenceAt a j) ∈
        Ideal.span ({algebraMap C.CoordinateRing
          (Localization (C.coordinateRingEvalSubmonoid a ha))
          (C.coordinateDifferenceAt a 0)} : Set _) := by
  intro j
  fin_cases j
  · exact Ideal.mem_span_singleton_self _
  · apply localization_left_mem_span_right_of_relation
      (C.coordinateRingEvalSubmonoid a ha)
      (C.coordinateDifferenceAt a 1) (C.coordinateDifferenceAt a 0) q₁ q₀
    · simpa only [add_comm] using hrel
    · rw [C.mem_coordinateRingEvalSubmonoid]
      exact fun hker ↦ hq₁ (RingHom.mem_ker.mp hker)


theorem exists_coordinateDifferences_mem_span_of_relation_of_coefficient_ne_zero
    (C : IrreduciblePlanePolynomial ℝ) (a : PachDeZeeuw.Algebraic.Point2)
    (ha : a ∈ PlaneCurveZeroSet C.polynomial) (q₀ q₁ : C.CoordinateRing)
    (hrel :
      C.coordinateDifferenceAt a 0 * q₀ +
          C.coordinateDifferenceAt a 1 * q₁ = 0)
    (hcoeff :
      C.coordinateRingEval a ha q₀ ≠ 0 ∨
        C.coordinateRingEval a ha q₁ ≠ 0) :
    ∃ i : Fin 2, ∀ j,
      algebraMap C.CoordinateRing
          (Localization (C.coordinateRingEvalSubmonoid a ha))
          (C.coordinateDifferenceAt a j) ∈
        Ideal.span ({algebraMap C.CoordinateRing
          (Localization (C.coordinateRingEvalSubmonoid a ha))
          (C.coordinateDifferenceAt a i)} : Set _) := by
  rcases hcoeff with hq₀ | hq₁
  · exact ⟨1,
      C.coordinateDifferences_mem_span_one_of_relation_of_leftCoefficient_ne_zero
        a ha q₀ q₁ hrel hq₀⟩
  · exact ⟨0,
      C.coordinateDifferences_mem_span_zero_of_relation_of_rightCoefficient_ne_zero
        a ha q₀ q₁ hrel hq₁⟩


end IrreduciblePlanePolynomial

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open PachDeZeeuw


@[simp]
theorem mem_carrierSymmetriesFinset
    {d : ℕ} {C : Set Point2}
    (hcurve : CurveSymmetries.IsIrreducibleCurve d C)
    (hnot : ¬ CurveSymmetries.IsLineOrCircle C)
    (g : Point2 ≃ᵢ Point2) :
    g ∈ carrierSymmetriesFinset hcurve hnot ↔ g '' C = C := by
  classical
  letI : Fintype (CarrierSymmetry C) :=
    carrierSymmetryFintype_of_lemma25 hcurve hnot
  change g ∈ (Finset.univ : Finset (CarrierSymmetry C)).image Subtype.val ↔ _
  constructor
  · intro hg
    obtain ⟨g', _hg', hgg'⟩ := Finset.mem_image.mp hg
    rw [← hgg']
    exact g'.property
  · intro hg
    exact Finset.mem_image.mpr ⟨⟨g, hg⟩, Finset.mem_univ _, rfl⟩

theorem carrierSymmetriesFinset_card_le
    {d : ℕ} {C : Set Point2}
    (hcurve : CurveSymmetries.IsIrreducibleCurve d C)
    (hnot : ¬ CurveSymmetries.IsLineOrCircle C) :
    (carrierSymmetriesFinset hcurve hnot).card ≤ 4 * d := by
  apply CurveSymmetries.lemma25 d C hcurve hnot
  intro g hg
  exact (mem_carrierSymmetriesFinset hcurve hnot g).1 hg


@[simp]
theorem mem_selfCurveCarrierSymmetries
    {d : ℕ} {X : PreparedBipartiteInput d}
    (hself : SelfCurvePreparedInput X) (g : Point2 ≃ᵢ Point2) :
    g ∈ selfCurveCarrierSymmetries hself ↔ g '' X.C₂ = X.C₂ :=
  mem_carrierSymmetriesFinset (preparedSecondCurve_isIrreducibleCurve X)
    (selfCurvePreparedInput_not_isLineOrCircle hself) g

theorem selfCurveCarrierSymmetries_card_le
    {d : ℕ} {X : PreparedBipartiteInput d}
    (hself : SelfCurvePreparedInput X) :
    (selfCurveCarrierSymmetries hself).card ≤ 4 * d :=
  carrierSymmetriesFinset_card_le
    (preparedSecondCurve_isIrreducibleCurve X)
    (selfCurvePreparedInput_not_isLineOrCircle hself)


theorem selfCurveCompleteSymmetryFamily_deletedLabels_card_le_eight_mul_degree_sq
    {d : ℕ} (X : PreparedBipartiteInput d)
    (hself : SelfCurvePreparedInput X)
    (reflections : Finset (Point2 ≃ᵢ Point2))
    (hd : 2 ≤ d)
    (hreflections : reflections.card ≤ 2 * d)
    (hfixed : ∀ g ∈ reflections, (selfCurveFixedAnchorsFor X g).card ≤ d) :
    (selfCurveDeletedLabels X
      (selfCurveExceptionalAnchors X
        (selfCurveAxisAnchorsFromReflections X reflections))
      (selfCurveSymmetryLabels X (selfCurveCarrierSymmetries hself))).card ≤
      8 * d ^ 2 * X.P₁.card := by
  have hsingular : (selfCurveSingularAnchors X).card ≤
      d * (d - 1) := by
    exact selfCurveSingularAnchors_card_le_degree_mul_pred_degree X
  have haxis :
      (selfCurveAxisAnchorsFromReflections X reflections).card ≤ 2 * d ^ 2 :=
    selfCurveAxisAnchorsFromReflections_card_le_two_mul_degree_sq
      X reflections hreflections hfixed
  have hΓ :
      (selfCurveSymmetryLabels X (selfCurveCarrierSymmetries hself)).card ≤
        4 * d * X.P₁.card :=
    selfCurveSymmetryLabels_card_le_four_mul_degree_mul_card X
      (selfCurveCarrierSymmetries hself) (selfCurveCarrierSymmetries_card_le hself)
  simpa [selfCurveDeletedLabels, selfCurveExceptionalAnchors] using
    (deletedIndexedPairs_card_le_eight_mul_degree_sq
      (S := (Finset.univ : Finset X.P₁))
      (singular := selfCurveSingularAnchors X)
      (axis := selfCurveAxisAnchorsFromReflections X reflections)
      (Γ := selfCurveSymmetryLabels X (selfCurveCarrierSymmetries hself))
      hd hsingular haxis (by simpa using hΓ))


end Esgk

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace MvPolynomial

 
theorem homogeneousComponent_map_star {σ : Type*} (m : ℕ) (P : MvPolynomial σ ℂ) :
    homogeneousComponent m (map (starRingEnd ℂ) P) =
      map (starRingEnd ℂ) (homogeneousComponent m P) := by
  ext d
  simp only [coeff_homogeneousComponent, coeff_map]
  split <;> simp_all

end MvPolynomial

namespace Esgk

open PachDeZeeuw.Algebraic _root_.Polynomial

variable {n : ℕ}

 
theorem circularChartDehomogenization_map_star (T : CircularChartPoly) :
    circularChartDehomogenization (MvPolynomial.map (starRingEnd ℂ) T) =
      Polynomial.map (starRingEnd ℂ) (circularChartDehomogenization T) := by
  induction T using MvPolynomial.induction_on with
  | C r => simp [circularChartDehomogenization]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, hP]
      fin_cases i <;> simp [circularChartDehomogenization]


theorem circularJTangentPolynomial_eq_map_star (G : PlanePoly) :
    circularJTangentPolynomial G =
      Polynomial.map (starRingEnd ℂ) (circularITangentPolynomial G) := by
  rw [circularJTangentPolynomial, circularITangentPolynomial,
    ← planeCircularLocalOrderI_eq_planeCircularLocalOrderJ G,
    ← projectiveCircularChartI_planeHomogenization_map_star G,
    MvPolynomial.homogeneousComponent_map_star,
    circularChartDehomogenization_map_star]


end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

namespace IrreduciblePlanePolynomial

open MvPolynomial


@[simp]
theorem specializeAt_X {R : Type*} [CommRing R] {σ : Type*} [DecidableEq σ]
    (i : σ) (c : R) (k : σ) :
    specializeAt i c (X k) = if k = i then C c else X k := by
  simp [specializeAt]


theorem eval₂_specializeAt {R : Type*} [CommRing R] {σ : Type*}
    [DecidableEq σ] (i : σ) (c : R) (a : σ → R) (ha : a i = c)
    (p : MvPolynomial σ R) :
    eval₂ (RingHom.id R) a (specializeAt i c p) =
      eval₂ (RingHom.id R) a p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [specializeAt]
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp =>
      simp only [map_mul, eval₂_mul, eval₂_X, hp, specializeAt_X]
      split_ifs with h
      · simp [h, ha]
      · simp


theorem specializeAt_fin2_fin2 {R : Type*} [CommRing R]
    (a : Fin 2 → R) (p : MvPolynomial (Fin 2) R) :
    specializeAt 0 (a 0) (specializeAt 1 (a 1) p) =
      C (eval₂ (RingHom.id R) a p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [specializeAt]
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp =>
      simp only [map_mul, hp, specializeAt_X]
      fin_cases n <;> simp [specializeAt]


theorem specializeAt_fin2_fin2_swap {R : Type*} [CommRing R]
    (a : Fin 2 → R) (p : MvPolynomial (Fin 2) R) :
    specializeAt 1 (a 1) (specializeAt 0 (a 0) p) =
      C (eval₂ (RingHom.id R) a p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [specializeAt]
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp =>
      simp only [map_mul, hp, specializeAt_X]
      fin_cases n <;> simp [specializeAt]


theorem exists_sub_eq_mul_specializeAt {R : Type*} [CommRing R] {σ : Type*}
    [DecidableEq σ] (i : σ) (c : R) (a : σ → R) (ha : a i = c)
    (p : MvPolynomial σ R) :
    ∃ q : MvPolynomial σ R,
      p - specializeAt i c p = (X i - C c) * q ∧
      eval₂ (RingHom.id R) a q =
        eval₂ (RingHom.id R) a (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
      refine ⟨0, ?_, ?_⟩ <;> simp [specializeAt]
  | add p q hp hq =>
      obtain ⟨up, hup, hep⟩ := hp
      obtain ⟨uq, huq, heq⟩ := hq
      refine ⟨up + uq, ?_, ?_⟩
      · rw [map_add]
        calc
          p + q - (specializeAt i c p + specializeAt i c q) =
              (p - specializeAt i c p) +
                (q - specializeAt i c q) := by ring
          _ = (X i - C c) * up + (X i - C c) * uq := by rw [hup, huq]
          _ = (X i - C c) * (up + uq) := by ring
      · simp only [eval₂_add, hep, heq, map_add]
  | mul_X p n hp =>
      obtain ⟨q, hq, heq⟩ := hp
      by_cases hni : n = i
      · subst n
        refine ⟨q * X i + specializeAt i c p, ?_, ?_⟩
        · rw [map_mul, specializeAt_X]
          rw [if_pos (Eq.refl i)]
          calc
            p * X i - specializeAt i c p * C c =
                (p - specializeAt i c p) * X i +
                  specializeAt i c p * (X i - C c) := by ring
            _ = (X i - C c) * (q * X i + specializeAt i c p) := by
              rw [hq]
              ring
        · simp [heq, eval₂_specializeAt i c a ha p, ha]
          ring
      · refine ⟨q * X n, ?_, ?_⟩
        · rw [map_mul, specializeAt_X]
          simp only [if_neg hni]
          calc
            p * X n - specializeAt i c p * X n =
                (p - specializeAt i c p) * X n := by ring
            _ = (X i - C c) * (q * X n) := by rw [hq]; ring
        · simp only [eval₂_mul, eval₂_X, heq]
          simp only [pderiv_mul, pderiv_X_of_ne hni, mul_zero,
            add_zero, eval₂_mul, eval₂_X]


theorem localized_generator_of_deriv_zero
    (C : IrreduciblePlanePolynomial ℝ) (a : PachDeZeeuw.Algebraic.Point2)
    (ha : a ∈ PlaneCurveZeroSet C.polynomial)
    (hderiv : MvPolynomial.eval (fun k => a k)
      (MvPolynomial.pderiv 0 C.polynomial) ≠ 0) :
    ∃ i : Fin 2, ∀ j,
      algebraMap C.CoordinateRing
          (Localization (C.coordinateRingEvalSubmonoid a ha))
          (C.coordinateDifferenceAt a j) ∈
        Ideal.span ({algebraMap C.CoordinateRing
          (Localization (C.coordinateRingEvalSubmonoid a ha))
          (C.coordinateDifferenceAt a i)} : Set _) := by
  let I : Ideal (MvPolynomial (Fin 2) ℝ) :=
    Ideal.span ({C.polynomial} : Set (MvPolynomial (Fin 2) ℝ))
  let mk : MvPolynomial (Fin 2) ℝ →+* C.CoordinateRing := Ideal.Quotient.mk I
  obtain ⟨q, hq, heq⟩ := exists_sub_eq_mul_specializeAt
    (R := ℝ) 0 (a 0) a rfl C.polynomial
  obtain ⟨r, hr, _her⟩ := exists_sub_eq_mul_specializeAt
    (R := ℝ) 1 (a 1) a rfl (specializeAt 0 (a 0) C.polynomial)
  have hconst : specializeAt 1 (a 1) (specializeAt 0 (a 0) C.polynomial) =
      MvPolynomial.C (MvPolynomial.eval (fun k => a k) C.polynomial) := by
    simpa only [MvPolynomial.eval₂_id] using
      specializeAt_fin2_fin2_swap a C.polynomial
  have heval : MvPolynomial.eval (fun k => a k) C.polynomial = 0 := by
    simpa only [mem_PlaneCurveZeroSet] using ha
  have hdecomp : C.polynomial =
      (X 0 - MvPolynomial.C (a 0)) * q +
        (X 1 - MvPolynomial.C (a 1)) * r := by
    calc
      C.polynomial = (C.polynomial - specializeAt 0 (a 0) C.polynomial) +
          (specializeAt 0 (a 0) C.polynomial -
            specializeAt 1 (a 1) (specializeAt 0 (a 0) C.polynomial)) := by
              rw [hconst, heval]
              simp
      _ = (X 0 - MvPolynomial.C (a 0)) * q +
          (X 1 - MvPolynomial.C (a 1)) * r := by rw [hq, hr]
  have hmkf : mk C.polynomial = 0 := by
    apply (Ideal.Quotient.eq_zero_iff_mem).2
    exact Ideal.subset_span (Set.mem_singleton C.polynomial)
  have hmkC (x : ℝ) :
      mk (MvPolynomial.C x) = algebraMap ℝ C.CoordinateRing x := by
    dsimp [mk, I]
    rw [MvPolynomial.C_eq_algebraMap]
    rfl
  have hrel : C.coordinateDifferenceAt a 0 * mk q +
      C.coordinateDifferenceAt a 1 * mk r = 0 := by
    have hmkrel : mk ((X 0 - MvPolynomial.C (a 0)) * q +
        (X 1 - MvPolynomial.C (a 1)) * r) = 0 := by
      rw [← hdecomp, hmkf]
    simp only [map_add, map_mul, map_sub, hmkC] at hmkrel
    simpa [mk, coordinateDifferenceAt, coordinateClass, I] using hmkrel
  have hqeval : C.coordinateRingEval a ha (mk q) ≠ 0 := by
    intro hzero
    apply hderiv
    have hzero' : MvPolynomial.eval₂ (RingHom.id ℝ) (fun k => a k) q = 0 := by
      set_option backward.isDefEq.respectTransparency false in
        simpa [mk, I, coordinateRingEval] using hzero
    have heq' : MvPolynomial.eval₂ (RingHom.id ℝ) (fun k => a k) q =
        MvPolynomial.eval₂ (RingHom.id ℝ) (fun k => a k)
          (MvPolynomial.pderiv 0 C.polynomial) := by simpa using heq
    rw [heq'] at hzero'
    simpa only [MvPolynomial.eval₂_id] using hzero'
  exact C.exists_coordinateDifferences_mem_span_of_relation_of_coefficient_ne_zero
    a ha (mk q) (mk r) hrel (Or.inl hqeval)


theorem localized_generator_of_deriv_one
    (C : IrreduciblePlanePolynomial ℝ) (a : PachDeZeeuw.Algebraic.Point2)
    (ha : a ∈ PlaneCurveZeroSet C.polynomial)
    (hderiv : MvPolynomial.eval (fun k => a k)
      (MvPolynomial.pderiv 1 C.polynomial) ≠ 0) :
    ∃ i : Fin 2, ∀ j,
      algebraMap C.CoordinateRing
          (Localization (C.coordinateRingEvalSubmonoid a ha))
          (C.coordinateDifferenceAt a j) ∈
        Ideal.span ({algebraMap C.CoordinateRing
          (Localization (C.coordinateRingEvalSubmonoid a ha))
          (C.coordinateDifferenceAt a i)} : Set _) := by
  let I : Ideal (MvPolynomial (Fin 2) ℝ) :=
    Ideal.span ({C.polynomial} : Set (MvPolynomial (Fin 2) ℝ))
  let mk : MvPolynomial (Fin 2) ℝ →+* C.CoordinateRing := Ideal.Quotient.mk I
  obtain ⟨q, hq, heq⟩ := exists_sub_eq_mul_specializeAt
    (R := ℝ) 1 (a 1) a rfl C.polynomial
  obtain ⟨r, hr, _her⟩ := exists_sub_eq_mul_specializeAt
    (R := ℝ) 0 (a 0) a rfl (specializeAt 1 (a 1) C.polynomial)
  have hconst : specializeAt 0 (a 0) (specializeAt 1 (a 1) C.polynomial) =
      MvPolynomial.C (MvPolynomial.eval (fun k => a k) C.polynomial) := by
    simpa only [MvPolynomial.eval₂_id] using
      specializeAt_fin2_fin2 a C.polynomial
  have heval : MvPolynomial.eval (fun k => a k) C.polynomial = 0 := by
    simpa only [mem_PlaneCurveZeroSet] using ha
  have hdecomp : C.polynomial =
      (X 1 - MvPolynomial.C (a 1)) * q +
        (X 0 - MvPolynomial.C (a 0)) * r := by
    calc
      C.polynomial = (C.polynomial - specializeAt 1 (a 1) C.polynomial) +
          (specializeAt 1 (a 1) C.polynomial -
            specializeAt 0 (a 0) (specializeAt 1 (a 1) C.polynomial)) := by
              rw [hconst, heval]
              simp
      _ = (X 1 - MvPolynomial.C (a 1)) * q +
          (X 0 - MvPolynomial.C (a 0)) * r := by rw [hq, hr]
  have hmkf : mk C.polynomial = 0 := by
    apply (Ideal.Quotient.eq_zero_iff_mem).2
    exact Ideal.subset_span (Set.mem_singleton C.polynomial)
  have hmkC (x : ℝ) :
      mk (MvPolynomial.C x) = algebraMap ℝ C.CoordinateRing x := by
    dsimp [mk, I]
    rw [MvPolynomial.C_eq_algebraMap]
    rfl
  have hrel : C.coordinateDifferenceAt a 1 * mk q +
      C.coordinateDifferenceAt a 0 * mk r = 0 := by
    have hmkrel : mk ((X 1 - MvPolynomial.C (a 1)) * q +
        (X 0 - MvPolynomial.C (a 0)) * r) = 0 := by
      rw [← hdecomp, hmkf]
    simp only [map_add, map_mul, map_sub, hmkC] at hmkrel
    simpa [mk, coordinateDifferenceAt, coordinateClass, I] using hmkrel
  have hqeval : C.coordinateRingEval a ha (mk q) ≠ 0 := by
    intro hzero
    apply hderiv
    have hzero' : MvPolynomial.eval₂ (RingHom.id ℝ) (fun k => a k) q = 0 := by
      set_option backward.isDefEq.respectTransparency false in
        simpa [mk, I, coordinateRingEval] using hzero
    have heq' : MvPolynomial.eval₂ (RingHom.id ℝ) (fun k => a k) q =
        MvPolynomial.eval₂ (RingHom.id ℝ) (fun k => a k)
          (MvPolynomial.pderiv 1 C.polynomial) := by simpa using heq
    rw [heq'] at hzero'
    simpa only [MvPolynomial.eval₂_id] using hzero'
  exact C.exists_coordinateDifferences_mem_span_of_relation_of_coefficient_ne_zero
    a ha (mk r) (mk q) (by simpa only [add_comm] using hrel) (Or.inr hqeval)

 
theorem localized_coordinateDifference_generator_of_smooth
    (C : IrreduciblePlanePolynomial ℝ) (a : PachDeZeeuw.Algebraic.Point2)
    (ha : a ∈ PlaneCurveZeroSet C.polynomial)
    (hsmooth :
      MvPolynomial.eval (fun k => a k) (MvPolynomial.pderiv 0 C.polynomial) ≠ 0 ∨
      MvPolynomial.eval (fun k => a k) (MvPolynomial.pderiv 1 C.polynomial) ≠ 0) :
    ∃ i : Fin 2, ∀ j,
      algebraMap C.CoordinateRing
          (Localization (C.coordinateRingEvalSubmonoid a ha))
          (C.coordinateDifferenceAt a j) ∈
        Ideal.span ({algebraMap C.CoordinateRing
          (Localization (C.coordinateRingEvalSubmonoid a ha))
          (C.coordinateDifferenceAt a i)} : Set _) := by
  rcases hsmooth with hzero | hone
  · exact C.localized_generator_of_deriv_zero a ha hzero
  · exact C.localized_generator_of_deriv_one a ha hone


theorem localized_coordinateDifference_generator_of_nonsingular
    (C : IrreduciblePlanePolynomial ℝ) (a : PachDeZeeuw.Algebraic.Point2)
    (ha : a ∈ PlaneCurveZeroSet C.polynomial)
    (hnonsingular : a ∉ SingularPointSet C.polynomial) :
    ∃ i : Fin 2, ∀ j,
      algebraMap C.CoordinateRing
          (Localization (C.coordinateRingEvalSubmonoid a ha))
          (C.coordinateDifferenceAt a j) ∈
        Ideal.span ({algebraMap C.CoordinateRing
          (Localization (C.coordinateRingEvalSubmonoid a ha))
          (C.coordinateDifferenceAt a i)} : Set _) := by
  apply C.localized_coordinateDifference_generator_of_smooth a ha
  by_cases hzero :
      MvPolynomial.eval (fun k => a k)
        (MvPolynomial.pderiv 0 C.polynomial) = 0
  · right
    intro hzero'
    exact hnonsingular ⟨⟨ha, hzero⟩, hzero'⟩
  · exact Or.inl hzero


theorem exists_point_and_comap_basePoint_eq_and_dist_eq_of_infinite_intersection_of_nonsingular
    (C : IrreduciblePlanePolynomial ℝ)
    (g₁ g₂ : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) {r₁ r₂ : ℝ}
    (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0)
    (hns₁ :
      xAxisReflectionPoint ''
          PlaneCurveZeroSet (C.affineIsometryTransport g₁).polynomial ≠
        PlaneCurveZeroSet (C.affineIsometryTransport g₁).polynomial)
    (hns₂ :
      xAxisReflectionPoint ''
          PlaneCurveZeroSet (C.affineIsometryTransport g₂).polynomial ≠
        PlaneCurveZeroSet (C.affineIsometryTransport g₂).polynomial)
    (a c b d : PachDeZeeuw.Algebraic.Point2)
    (hg₁a : g₁ a = xAxisPoint (-r₁))
    (hg₁c : g₁ c = xAxisPoint r₁)
    (hg₂b : g₂ b = xAxisPoint (-r₂))
    (hg₂d : g₂ d = xAxisPoint r₂)
    (hinf : (twoPairDistanceCommonZeroSet C a c b d).Infinite)
    (ha : a ∈ PlaneCurveZeroSet C.polynomial)
    (hnonsingular : a ∉ SingularPointSet C.polynomial) :
    ∃ x : C.RealAffineNormalizationPoint,
      ∃ degreeRight : C.affineNormalizationRing ≃ₐ[ℝ] C.affineNormalizationRing,
        x.basePoint = a ∧ (x.comap degreeRight).basePoint = b ∧ dist a c = dist b d := by
  obtain ⟨i, hgen⟩ :=
    C.localized_coordinateDifference_generator_of_nonsingular a ha hnonsingular
  exact
    C.exists_point_and_comap_basePoint_eq_and_dist_eq_of_infinite_intersection_of_coordinateDifference_generator
      g₁ g₂ hr₁ hr₂ hns₁ hns₂ a c b d hg₁a hg₁c hg₂b hg₂d hinf ha i hgen

end IrreduciblePlanePolynomial

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open PachDeZeeuw


theorem planeIsometryLinearPart_one_eq :
    planeIsometryLinearPart
      (1 : IsometryEquiv CurveSymmetries.Point2
        CurveSymmetries.Point2) = 1 := by
  apply LinearIsometryEquiv.ext
  intro x
  have h := planeIsometry_apply_eq_linearPart_add
    (1 : IsometryEquiv CurveSymmetries.Point2
      CurveSymmetries.Point2) x
  simpa using h.symm

 
theorem IsDirect.one :
    IsDirect (1 : IsometryEquiv CurveSymmetries.Point2
      CurveSymmetries.Point2) := by
  change 0 < LinearMap.det
    ((planeIsometryLinearPart
      (1 : IsometryEquiv CurveSymmetries.Point2
        CurveSymmetries.Point2)).toLinearEquiv :
      CurveSymmetries.Point2 →ₗ[ℝ] CurveSymmetries.Point2)
  rw [planeIsometryLinearPart_one_eq]
  change 0 < LinearMap.det
    (LinearMap.id : CurveSymmetries.Point2 →ₗ[ℝ]
      CurveSymmetries.Point2)
  rw [LinearMap.det_id]
  norm_num

 
theorem isometryEquiv_ne_one_of_not_isDirect
    {g : IsometryEquiv CurveSymmetries.Point2 CurveSymmetries.Point2}
    (hg : ¬ IsDirect g) : g ≠ 1 := by
  intro hgone
  subst g
  exact hg IsDirect.one

 
theorem CurveSymmetries.lemma25Direct :
    CurveSymmetries.Lemma25DirectStatement :=
  CurveSymmetries.lemma25Direct_of_commonFixedPoint
    (CurveSymmetries.directSymmetriesHaveCommonFixedPoint_of_noTranslations
      CurveSymmetries.noNontrivialTranslationSymmetry)


theorem CurveSymmetries.reversingSymmetries_card_le
    {d : ℕ} {C : Set CurveSymmetries.Point2}
    (hcurve : CurveSymmetries.IsIrreducibleCurve d C)
    (hnot : ¬ CurveSymmetries.IsLineOrCircle C)
    (symmetries : Finset
      (IsometryEquiv CurveSymmetries.Point2 CurveSymmetries.Point2))
    (hreversing : ∀ g ∈ symmetries, ¬ IsDirect g)
    (hpreserves : ∀ g ∈ symmetries, g '' C = C) :
    symmetries.card ≤ 2 * d := by
  classical
  by_cases hnonempty : symmetries.Nonempty
  · obtain ⟨r, hr⟩ := hnonempty
    let twist :
        IsometryEquiv CurveSymmetries.Point2 CurveSymmetries.Point2 ↪
          IsometryEquiv CurveSymmetries.Point2 CurveSymmetries.Point2 :=
      ⟨fun g ↦ r.trans g, isometryEquiv_trans_left_injective r⟩
    let twisted : Finset
        (IsometryEquiv CurveSymmetries.Point2 CurveSymmetries.Point2) :=
      symmetries.map twist
    have hrReversing : ¬ IsDirect r := hreversing r hr
    have hrPreserves : r '' C = C := hpreserves r hr
    have htwistedDirect : ∀ g ∈ twisted, IsDirect g := by
      intro g hg
      obtain ⟨h, hh, rfl⟩ := Finset.mem_map.mp hg
      exact IsDirect.trans_of_not hrReversing (hreversing h hh)
    have htwistedPreserves : ∀ g ∈ twisted, g '' C = C := by
      intro g hg
      obtain ⟨h, hh, rfl⟩ := Finset.mem_map.mp hg
      exact isometryEquiv_trans_image_eq hrPreserves (hpreserves h hh)
    rw [← Finset.card_map]
    exact CurveSymmetries.lemma25Direct d C hcurve hnot twisted
      htwistedDirect htwistedPreserves
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hnonempty,
      Finset.card_empty, Nat.zero_le]


@[simp]
theorem mem_selfCurveReversingCarrierSymmetries
    {d : ℕ} {X : PreparedBipartiteInput d}
    (hself : SelfCurvePreparedInput X) (g : Point2 ≃ᵢ Point2) :
    g ∈ selfCurveReversingCarrierSymmetries hself ↔
      g '' X.C₂ = X.C₂ ∧ ¬ IsDirect g := by
  classical
  simp [selfCurveReversingCarrierSymmetries,
    mem_selfCurveCarrierSymmetries hself]


theorem selfCurveReversingCarrierSymmetries_card_le
    {d : ℕ} {X : PreparedBipartiteInput d}
    (hself : SelfCurvePreparedInput X) :
    (selfCurveReversingCarrierSymmetries hself).card ≤ 2 * d := by
  apply CurveSymmetries.reversingSymmetries_card_le
      (preparedSecondCurve_isIrreducibleCurve X)
      (selfCurvePreparedInput_not_isLineOrCircle hself)
  · intro g hg
    exact (mem_selfCurveReversingCarrierSymmetries hself g).1 hg |>.2
  · intro g hg
    exact (mem_selfCurveReversingCarrierSymmetries hself g).1 hg |>.1

end Esgk

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open _root_.Polynomial
open PachDeZeeuw.Algebraic


theorem exists_simultaneously_centered_circular_tangent_polynomials
    {G : PlanePoly} {p : ℕ}
    (hI : circularITangentPolynomial G ≠ 0)
    (hdegree : (circularITangentPolynomial G).natDegree = p)
    (hroots : (circularITangentPolynomial G).roots.toFinset.card = 1) :
    ∃ ξ : ℂ,
      (circularITangentPolynomial G).comp
          (Polynomial.X + Polynomial.C (Complex.I * ξ)) =
        Polynomial.C (circularITangentPolynomial G).leadingCoeff * Polynomial.X ^ p ∧
      (circularJTangentPolynomial G).comp
          (Polynomial.X + Polynomial.C (-Complex.I * star ξ)) =
        Polynomial.C (star (circularITangentPolynomial G).leadingCoeff) *
          Polynomial.X ^ p := by
  obtain ⟨τ, hfactor⟩ :=
    Polynomial.exists_eq_C_leadingCoeff_mul_X_sub_C_pow_natDegree_of_roots_toFinset_card_eq_one
      (circularITangentPolynomial G) hI hroots
  refine ⟨-Complex.I * τ, ?_, ?_⟩
  · nth_rewrite 1 [hfactor]
    rw [hdegree]
    rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp,
      Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
    have hshift : Complex.I * (-Complex.I * τ) = τ := by
      calc
        Complex.I * (-Complex.I * τ) = -(Complex.I * Complex.I) * τ := by ring
        _ = τ := by rw [Complex.I_mul_I]; ring
    rw [hshift]
    ring
  · rw [circularJTangentPolynomial_eq_map_star]
    nth_rewrite 1 [hfactor]
    rw [hdegree, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_sub, Polynomial.map_X,
      Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp,
      Polynomial.sub_comp, Polynomial.X_comp]
    have hshift : -Complex.I * star (-Complex.I * τ) = star τ := by
      have hconj : star (-Complex.I * τ) = Complex.I * star τ := by
        simp
      rw [hconj]
      calc
        -Complex.I * (Complex.I * star τ) =
            -(Complex.I * Complex.I) * star τ := by ring
        _ = star τ := by rw [Complex.I_mul_I]; ring
    rw [hshift]
    simp only [Polynomial.map_C, starRingEnd_apply]
    rw [Polynomial.C_comp]
    ring

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open MvPolynomial
open PachDeZeeuw.Algebraic

private theorem inline_Esgk_CircularTangentIsotropicFaces__circularChart_C_half_mul_two :
    (MvPolynomial.C (1 / 2 : ℂ) : CircularChartPoly) * 2 = 1 := by
  change MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.C (2 : ℂ) = MvPolynomial.C 1
  rw [← map_mul]
  norm_num

private theorem inline_Esgk_CircularTangentIsotropicFaces__circularChart_C_I_sq :
    (MvPolynomial.C Complex.I : CircularChartPoly) ^ 2 = -1 := by
  rw [← map_pow, Complex.I_sq, map_neg, map_one]


private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicAffineCircularChartIForFaces_planeToIsotropic_realToComplex
    (G : PlanePoly) :
    bundle_Esgk_CircularTangentIsotropicFaces_isotropicAffineCircularChartIForFaces
        (planeToIsotropicCoordinates (realToComplexPlanePolynomial G)) =
      affineCircularChartI G := by
  change
    (((bundle_Esgk_CircularTangentIsotropicFaces_isotropicAffineCircularChartIForFaces.comp planeToIsotropicCoordinates).comp
      realToComplexPlanePolynomial) G) = affineCircularChartI G
  apply RingHom.congr_fun
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [bundle_Esgk_CircularTangentIsotropicFaces_isotropicAffineCircularChartIForFaces, planeToIsotropicCoordinates,
      realToComplexPlanePolynomial, affineCircularChartI, affineCircularChart]
  · intro i
    fin_cases i <;>
      simp [bundle_Esgk_CircularTangentIsotropicFaces_isotropicAffineCircularChartIForFaces, planeToIsotropicCoordinates,
        realToComplexPlanePolynomial, affineCircularChartI, affineCircularChart,
        circularChartU]
    · simpa [mul_assoc] using inline_Esgk_CircularTangentIsotropicFaces__circularChart_C_half_mul_two
    · calc
        _ = (MvPolynomial.C Complex.I + circularChartU) *
            ((MvPolynomial.C (1 / 2 : ℂ) : CircularChartPoly) * 2) := by
          simp only [circularChartU]
          ring_nf
          rw [inline_Esgk_CircularTangentIsotropicFaces__circularChart_C_I_sq]
          ring
        _ = MvPolynomial.C Complex.I + circularChartU := by
          rw [inline_Esgk_CircularTangentIsotropicFaces__circularChart_C_half_mul_two, mul_one]

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicAffineCircularChartJForFaces_planeToIsotropic_realToComplex
    (G : PlanePoly) :
    bundle_Esgk_CircularTangentIsotropicFaces_isotropicAffineCircularChartJForFaces
        (planeToIsotropicCoordinates (realToComplexPlanePolynomial G)) =
      affineCircularChartJ G := by
  change
    (((bundle_Esgk_CircularTangentIsotropicFaces_isotropicAffineCircularChartJForFaces.comp planeToIsotropicCoordinates).comp
      realToComplexPlanePolynomial) G) = affineCircularChartJ G
  apply RingHom.congr_fun
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [bundle_Esgk_CircularTangentIsotropicFaces_isotropicAffineCircularChartJForFaces, planeToIsotropicCoordinates,
      realToComplexPlanePolynomial, affineCircularChartJ, affineCircularChart]
  · intro i
    fin_cases i <;>
      simp [bundle_Esgk_CircularTangentIsotropicFaces_isotropicAffineCircularChartJForFaces, planeToIsotropicCoordinates,
        realToComplexPlanePolynomial, affineCircularChartJ, affineCircularChart,
        circularChartU]
    · simpa [mul_assoc] using inline_Esgk_CircularTangentIsotropicFaces__circularChart_C_half_mul_two
    · calc
        _ = (-MvPolynomial.C Complex.I + circularChartU) *
            ((MvPolynomial.C (1 / 2 : ℂ) : CircularChartPoly) * 2) := by
          simp only [circularChartU]
          ring_nf
          rw [inline_Esgk_CircularTangentIsotropicFaces__circularChart_C_I_sq]
          ring
        _ = -MvPolynomial.C Complex.I + circularChartU := by
          rw [inline_Esgk_CircularTangentIsotropicFaces__circularChart_C_half_mul_two, mul_one]

private theorem inline_Esgk_CircularTangentIsotropicFaces__planeToIsotropicCoordinates_isHomogeneousForFaces
    {d : ℕ} {P : ComplexPlanePoly} (hP : P.IsHomogeneous d) :
    (planeToIsotropicCoordinates P).IsHomogeneous d := by
  change
    (MvPolynomial.eval₂ (MvPolynomial.C : ℂ →+* ComplexPlanePoly)
      ![MvPolynomial.C (1 / 2 : ℂ) * (MvPolynomial.X 0 + MvPolynomial.X 1),
        MvPolynomial.C (1 / (2 * Complex.I)) *
          (MvPolynomial.X 0 - MvPolynomial.X 1)] P).IsHomogeneous d
  have h := hP.eval₂
    (MvPolynomial.C : ℂ →+* ComplexPlanePoly)
    ![MvPolynomial.C (1 / 2 : ℂ) * (MvPolynomial.X 0 + MvPolynomial.X 1),
      MvPolynomial.C (1 / (2 * Complex.I)) *
        (MvPolynomial.X 0 - MvPolynomial.X 1)]
    (fun c ↦ MvPolynomial.isHomogeneous_C (Fin 2) c)
    (fun i ↦ by
      fin_cases i
      · exact ((MvPolynomial.isHomogeneous_X ℂ 0).add
          (MvPolynomial.isHomogeneous_X ℂ 1)).C_mul _
      · exact ((MvPolynomial.isHomogeneous_X ℂ 0).sub
          (MvPolynomial.isHomogeneous_X ℂ 1)).C_mul _)
  rw [Nat.one_mul] at h
  exact h

private theorem inline_Esgk_CircularTangentIsotropicFaces__planeToIsotropicCoordinates_homogeneousComponentForFaces
    (d : ℕ) (P : ComplexPlanePoly) :
    planeToIsotropicCoordinates (MvPolynomial.homogeneousComponent d P) =
      MvPolynomial.homogeneousComponent d (planeToIsotropicCoordinates P) := by
  classical
  by_cases hd : d ≤ P.totalDegree
  · have hsum :
        ∑ k ∈ Finset.range (P.totalDegree + 1),
            planeToIsotropicCoordinates (MvPolynomial.homogeneousComponent k P) =
          planeToIsotropicCoordinates P := by
      rw [← map_sum, MvPolynomial.sum_homogeneousComponent]
    have himage (k : ℕ) :
        (planeToIsotropicCoordinates
          (MvPolynomial.homogeneousComponent k P)).IsHomogeneous k :=
      inline_Esgk_CircularTangentIsotropicFaces__planeToIsotropicCoordinates_isHomogeneousForFaces
        (MvPolynomial.homogeneousComponent_isHomogeneous k P)
    symm
    calc
      MvPolynomial.homogeneousComponent d (planeToIsotropicCoordinates P) =
          MvPolynomial.homogeneousComponent d
            (∑ k ∈ Finset.range (P.totalDegree + 1),
              planeToIsotropicCoordinates (MvPolynomial.homogeneousComponent k P)) := by
        rw [hsum]
      _ = ∑ k ∈ Finset.range (P.totalDegree + 1),
          MvPolynomial.homogeneousComponent d
            (planeToIsotropicCoordinates (MvPolynomial.homogeneousComponent k P)) := by
        simp only [map_sum]
      _ = planeToIsotropicCoordinates (MvPolynomial.homogeneousComponent d P) := by
        simp_rw [MvPolynomial.homogeneousComponent_of_mem (himage _)]
        simp [hd]
  · have hPd : P.totalDegree < d := by omega
    have hTd : (planeToIsotropicCoordinates P).totalDegree < d := by
      rw [planeToIsotropicCoordinates_totalDegree]
      exact hPd
    rw [MvPolynomial.homogeneousComponent_eq_zero d P hPd, map_zero,
      MvPolynomial.homogeneousComponent_eq_zero d _ hTd]

private theorem inline_Esgk_CircularTangentIsotropicFaces__realToComplexPlanePolynomial_homogeneousComponentForFaces
    (d : ℕ) (G : PlanePoly) :
    realToComplexPlanePolynomial (MvPolynomial.homogeneousComponent d G) =
      MvPolynomial.homogeneousComponent d (realToComplexPlanePolynomial G) := by
  ext e
  simp only [realToComplexPlanePolynomial, MvPolynomial.coeff_map,
    MvPolynomial.coeff_homogeneousComponent]
  split_ifs <;> simp


private theorem inline_Esgk_CircularTangentIsotropicFaces__projectiveCircularChartI_planeHomogenization_eq_isotropicForFaces
    (D : ℕ) (G : PlanePoly) :
    projectiveCircularChartI (planeHomogenization D G) =
      bundle_Esgk_CircularTangentIsotropicFaces_isotropicHomogenizedCircularChartIForFaces D
        (planeToIsotropicCoordinates (realToComplexPlanePolynomial G)) := by
  rw [projectiveCircularChartI, projectiveCircularChart_planeHomogenization]
  rw [bundle_Esgk_CircularTangentIsotropicFaces_isotropicHomogenizedCircularChartIForFaces]
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  change affineCircularChartI (MvPolynomial.homogeneousComponent d G) = _
  rw [← inline_Esgk_CircularTangentIsotropicFaces__isotropicAffineCircularChartIForFaces_planeToIsotropic_realToComplex]
  congr 1
  rw [inline_Esgk_CircularTangentIsotropicFaces__realToComplexPlanePolynomial_homogeneousComponentForFaces,
    inline_Esgk_CircularTangentIsotropicFaces__planeToIsotropicCoordinates_homogeneousComponentForFaces]

private theorem inline_Esgk_CircularTangentIsotropicFaces__projectiveCircularChartJ_planeHomogenization_eq_isotropicForFaces
    (D : ℕ) (G : PlanePoly) :
    projectiveCircularChartJ (planeHomogenization D G) =
      bundle_Esgk_CircularTangentIsotropicFaces_isotropicHomogenizedCircularChartJForFaces D
        (planeToIsotropicCoordinates (realToComplexPlanePolynomial G)) := by
  rw [projectiveCircularChartJ, projectiveCircularChart_planeHomogenization]
  rw [bundle_Esgk_CircularTangentIsotropicFaces_isotropicHomogenizedCircularChartJForFaces]
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  change affineCircularChartJ (MvPolynomial.homogeneousComponent d G) = _
  rw [← inline_Esgk_CircularTangentIsotropicFaces__isotropicAffineCircularChartJForFaces_planeToIsotropic_realToComplex]
  congr 1
  rw [inline_Esgk_CircularTangentIsotropicFaces__realToComplexPlanePolynomial_homogeneousComponentForFaces,
    inline_Esgk_CircularTangentIsotropicFaces__planeToIsotropicCoordinates_homogeneousComponentForFaces]


@[simp]
theorem isotropicFaceExponent_zero (a b : ℕ) : isotropicFaceExponent a b 0 = a := by
  simp [isotropicFaceExponent]

@[simp]
theorem isotropicFaceExponent_one (a b : ℕ) : isotropicFaceExponent a b 1 = b := by
  simp [isotropicFaceExponent]

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicFaceExponent_eq_iff {a b c d : ℕ} :
    isotropicFaceExponent a b = isotropicFaceExponent c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    exact ⟨by simpa using DFunLike.congr_fun h 0,
      by simpa using DFunLike.congr_fun h 1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem inline_Esgk_CircularTangentIsotropicFaces__eq_isotropicFaceExponent_iff {e : Fin 2 →₀ ℕ} {a b : ℕ} :
    e = isotropicFaceExponent a b ↔ e 0 = a ∧ e 1 = b := by
  constructor
  · intro h
    exact ⟨by simpa using DFunLike.congr_fun h 0,
      by simpa using DFunLike.congr_fun h 1⟩
  · rintro ⟨hzero, hone⟩
    apply Finsupp.ext
    intro i
    fin_cases i
    · simp [hzero]
    · simp [hone]


theorem circularChartDehomogenization_homogeneousComponent_coeff
    (F : CircularChartPoly) (p a : ℕ) (ha : a ≤ p) :
    (circularChartDehomogenization (MvPolynomial.homogeneousComponent p F)).coeff a =
      MvPolynomial.coeff (isotropicFaceExponent a (p - a)) F := by
  let T := MvPolynomial.homogeneousComponent p F
  have hT : MvPolynomial.IsHomogeneous T p :=
    MvPolynomial.homogeneousComponent_isHomogeneous p F
  have hhomogenize : (circularChartDehomogenization T).homogenize p = T := by
    apply Polynomial.homogenize_eq_of_isHomogeneous hT
    rfl
  let e := isotropicFaceExponent a (p - a)
  calc
    (circularChartDehomogenization T).coeff a =
        MvPolynomial.coeff e ((circularChartDehomogenization T).homogenize p) := by
      rw [Polynomial.coeff_homogenize]
      simp [e, Nat.add_sub_of_le ha]
    _ = MvPolynomial.coeff e T := by rw [hhomogenize]
    _ = MvPolynomial.coeff e F := by
      have hedegree : Finsupp.degree e = p := by
        rw [Finsupp.degree_eq_sum]
        simp [e, Fin.sum_univ_two, Nat.add_sub_of_le ha]
      rw [MvPolynomial.coeff_homogeneousComponent, if_pos hedegree]

private theorem inline_Esgk_CircularTangentIsotropicFaces__coeff_circularChartZ_pow_mul_toMvPolynomial
    (P : Polynomial ℂ) (a b k : ℕ) :
    MvPolynomial.coeff (isotropicFaceExponent a b)
        (circularChartZ ^ k * Polynomial.toMvPolynomial 0 P) =
      if b = k then P.coeff a else 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simp only [map_add, mul_add, MvPolynomial.coeff_add, Polynomial.coeff_add, hP, hQ]
      by_cases hbk : b = k <;> simp [hbk]
  | monomial n c =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp only [map_mul, Polynomial.toMvPolynomial_C, map_pow,
        Polynomial.toMvPolynomial_X]
      have hpoly :
          circularChartZ ^ k *
              ((MvPolynomial.C c : CircularChartPoly) * MvPolynomial.X 0 ^ n) =
            MvPolynomial.monomial (isotropicFaceExponent n k) c := by
        rw [MvPolynomial.monomial_eq]
        simp [isotropicFaceExponent, Finsupp.prod_fintype, Fin.prod_univ_two,
          circularChartZ]
        ring
      rw [hpoly, MvPolynomial.coeff_monomial]
      simp only [inline_Esgk_CircularTangentIsotropicFaces__isotropicFaceExponent_eq_iff, Polynomial.coeff_C_mul_X_pow]
      by_cases hbk : b = k
      · subst b
        by_cases han : a = n
        · subst a
          simp
        · simp [han, Ne.symm han]
      · have hkb : k ≠ b := Ne.symm hbk
        by_cases han : a = n
        · subst a
          simp [hbk, hkb]
        · simp [hbk, hkb, Ne.symm han]

private theorem inline_Esgk_CircularTangentIsotropicFaces__homogenized_eval₂_eq_support_sumForFaces
    (D : ℕ) (Q : ComplexPlanePoly) (A B : CircularChartPoly)
    (hdegree : Q.totalDegree ≤ D) :
    (∑ d ∈ Finset.range (D + 1),
      circularChartZ ^ (D - d) *
        MvPolynomial.eval₂Hom (MvPolynomial.C : ℂ →+* CircularChartPoly) ![A, B]
          (MvPolynomial.homogeneousComponent d Q)) =
      ∑ e ∈ Q.support,
        MvPolynomial.C (MvPolynomial.coeff e Q) * A ^ e 0 * B ^ e 1 *
          circularChartZ ^ (D - e.degree) := by
  classical
  calc
    _ = ∑ d ∈ Finset.range (D + 1),
        ∑ e ∈ Q.support with e.degree = d,
          MvPolynomial.C (MvPolynomial.coeff e Q) * A ^ e 0 * B ^ e 1 *
            circularChartZ ^ (D - e.degree) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [MvPolynomial.homogeneousComponent_apply, map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      have hedegree : e.degree = d := (Finset.mem_filter.mp he).2
      rw [MvPolynomial.eval₂Hom_monomial]
      rw [hedegree]
      simp [Finsupp.prod_fintype, Fin.prod_univ_two]
      ring
    _ = ∑ e ∈ Q.support,
        MvPolynomial.C (MvPolynomial.coeff e Q) * A ^ e 0 * B ^ e 1 *
          circularChartZ ^ (D - e.degree) := by
      apply Finset.sum_fiberwise_of_maps_to
      intro e he
      rw [Finsupp.degree_eq_sum]
      simp only [Finset.mem_range, Nat.lt_add_one_iff]
      calc
        ∑ i, e i = e.sum (fun _ a ↦ a) :=
          (Finsupp.sum_fintype e (fun _ a ↦ a) (fun _ ↦ rfl)).symm
        _ ≤ D := (MvPolynomial.le_totalDegree he).trans hdegree


private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicHomogenizedCircularChartIForFaces_eq_support_sum
    (D : ℕ) (Q : ComplexPlanePoly) (hdegree : Q.totalDegree ≤ D) :
    bundle_Esgk_CircularTangentIsotropicFaces_isotropicHomogenizedCircularChartIForFaces D Q =
      ∑ e ∈ Q.support,
        bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartITermForFaces D e (MvPolynomial.coeff e Q) := by
  rw [bundle_Esgk_CircularTangentIsotropicFaces_isotropicHomogenizedCircularChartIForFaces]
  exact inline_Esgk_CircularTangentIsotropicFaces__homogenized_eval₂_eq_support_sumForFaces D Q _ _ hdegree

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicHomogenizedCircularChartJForFaces_eq_support_sum
    (D : ℕ) (Q : ComplexPlanePoly) (hdegree : Q.totalDegree ≤ D) :
    bundle_Esgk_CircularTangentIsotropicFaces_isotropicHomogenizedCircularChartJForFaces D Q =
      ∑ e ∈ Q.support,
        bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartJTermForFaces D e (MvPolynomial.coeff e Q) := by
  rw [bundle_Esgk_CircularTangentIsotropicFaces_isotropicHomogenizedCircularChartJForFaces]
  exact inline_Esgk_CircularTangentIsotropicFaces__homogenized_eval₂_eq_support_sumForFaces D Q _ _ hdegree


private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartITermForFaces_eq_toMvPolynomial
    (D : ℕ) (e : Fin 2 →₀ ℕ) (c : ℂ) :
    bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartITermForFaces D e c =
      circularChartZ ^ (D - e.degree) *
        Polynomial.toMvPolynomial 0 (bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartIPolynomialForFaces e c) := by
  simp [bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartITermForFaces, bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartIPolynomialForFaces,
    circularChartU, map_ofNat]
  ring

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartJTermForFaces_eq_toMvPolynomial
    (D : ℕ) (e : Fin 2 →₀ ℕ) (c : ℂ) :
    bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartJTermForFaces D e c =
      circularChartZ ^ (D - e.degree) *
        Polynomial.toMvPolynomial 0 (bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartJPolynomialForFaces e c) := by
  simp [bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartJTermForFaces, bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartJPolynomialForFaces,
    circularChartU, map_ofNat]
  ring

private theorem inline_Esgk_CircularTangentIsotropicFaces__finTwo_degree_eq_addForFaces (e : Fin 2 →₀ ℕ) :
    e.degree = e 0 + e 1 := by
  simp [Finsupp.degree_eq_sum, Fin.sum_univ_two]

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartIPolynomialForFaces_eq
    (e : Fin 2 →₀ ℕ) (c : ℂ) :
    bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartIPolynomialForFaces e c =
      Polynomial.C (c * Complex.I ^ e 0) * Polynomial.X ^ e 0 *
        (2 - Polynomial.C Complex.I * Polynomial.X) ^ e 1 := by
  rw [bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartIPolynomialForFaces, mul_pow, ← map_pow, map_mul]
  ring

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartJPolynomialForFaces_eq
    (e : Fin 2 →₀ ℕ) (c : ℂ) :
    bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartJPolynomialForFaces e c =
      Polynomial.C (c * (-Complex.I) ^ e 1) * Polynomial.X ^ e 1 *
        (2 + Polynomial.C Complex.I * Polynomial.X) ^ e 0 := by
  rw [bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartJPolynomialForFaces, mul_pow, ← map_neg, ← map_pow,
    map_mul]
  ring

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartITermForFaces_coeff_face
    (p a : ℕ) (ha : a ≤ p) (e : Fin 2 →₀ ℕ) (c : ℂ)
    (hebound : e 0 ≤ p ∧ e 1 ≤ p) :
    MvPolynomial.coeff (isotropicFaceExponent a (p - a))
        (bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartITermForFaces (2 * p) e c) =
      if e = isotropicFaceExponent a p
      then c * Complex.I ^ a * (2 : ℂ) ^ p
      else 0 := by
  rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartITermForFaces_eq_toMvPolynomial,
    inline_Esgk_CircularTangentIsotropicFaces__coeff_circularChartZ_pow_mul_toMvPolynomial]
  by_cases hz : p - a = 2 * p - e.degree
  · rw [if_pos hz]
    have hedegree_le : e.degree ≤ 2 * p := by
      rw [inline_Esgk_CircularTangentIsotropicFaces__finTwo_degree_eq_addForFaces]
      omega
    have hedegree : e.degree = p + a := by omega
    have hae : a ≤ e 0 := by
      rw [inline_Esgk_CircularTangentIsotropicFaces__finTwo_degree_eq_addForFaces] at hedegree
      omega
    rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartIPolynomialForFaces_eq]
    by_cases he : e = isotropicFaceExponent a p
    · subst e
      simp only [isotropicFaceExponent_zero, isotropicFaceExponent_one]
      simp only [if_true]
      rw [mul_assoc, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow_mul']
      simp [Polynomial.coeff_zero_eq_eval_zero]
    · rw [if_neg he, mul_assoc, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow_mul']
      have hene : e 0 ≠ a := by
        intro hezero
        apply he
        apply Finsupp.ext
        intro i
        fin_cases i
        · simp [hezero]
        · rw [inline_Esgk_CircularTangentIsotropicFaces__finTwo_degree_eq_addForFaces] at hedegree
          simp
          omega
      have hlt : a < e 0 := lt_of_le_of_ne hae (Ne.symm hene)
      simp [not_le.mpr hlt]
  · rw [if_neg hz, if_neg]
    intro he
    subst e
    apply hz
    rw [inline_Esgk_CircularTangentIsotropicFaces__finTwo_degree_eq_addForFaces]
    simp
    omega

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartJTermForFaces_coeff_face
    (p b : ℕ) (hb : b ≤ p) (e : Fin 2 →₀ ℕ) (c : ℂ)
    (hebound : e 0 ≤ p ∧ e 1 ≤ p) :
    MvPolynomial.coeff (isotropicFaceExponent b (p - b))
        (bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartJTermForFaces (2 * p) e c) =
      if e = isotropicFaceExponent p b
      then c * (-Complex.I) ^ b * (2 : ℂ) ^ p
      else 0 := by
  rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartJTermForFaces_eq_toMvPolynomial,
    inline_Esgk_CircularTangentIsotropicFaces__coeff_circularChartZ_pow_mul_toMvPolynomial]
  by_cases hz : p - b = 2 * p - e.degree
  · rw [if_pos hz]
    have hedegree_le : e.degree ≤ 2 * p := by
      rw [inline_Esgk_CircularTangentIsotropicFaces__finTwo_degree_eq_addForFaces]
      omega
    have hedegree : e.degree = p + b := by omega
    have hbe : b ≤ e 1 := by
      rw [inline_Esgk_CircularTangentIsotropicFaces__finTwo_degree_eq_addForFaces] at hedegree
      omega
    rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartJPolynomialForFaces_eq]
    by_cases he : e = isotropicFaceExponent p b
    · subst e
      simp only [isotropicFaceExponent_zero, isotropicFaceExponent_one]
      simp only [if_true]
      rw [mul_assoc, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow_mul']
      simp [Polynomial.coeff_zero_eq_eval_zero]
    · rw [if_neg he, mul_assoc, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow_mul']
      have hene : e 1 ≠ b := by
        intro heone
        apply he
        apply Finsupp.ext
        intro i
        fin_cases i
        · rw [inline_Esgk_CircularTangentIsotropicFaces__finTwo_degree_eq_addForFaces] at hedegree
          simp
          omega
        · simp [heone]
      have hlt : b < e 1 := lt_of_le_of_ne hbe (Ne.symm hene)
      simp [not_le.mpr hlt]
  · rw [if_neg hz, if_neg]
    intro he
    subst e
    apply hz
    rw [inline_Esgk_CircularTangentIsotropicFaces__finTwo_degree_eq_addForFaces]
    simp
    omega

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicHomogenizedCircularChartIForFaces_coeff_face
    (Q : ComplexPlanePoly) (p a : ℕ) (ha : a ≤ p) (hbound : BidegreeBound p Q) :
    MvPolynomial.coeff (isotropicFaceExponent a (p - a))
        (bundle_Esgk_CircularTangentIsotropicFaces_isotropicHomogenizedCircularChartIForFaces (2 * p) Q) =
      (2 : ℂ) ^ p * Complex.I ^ a *
        MvPolynomial.coeff (isotropicFaceExponent a p) Q := by
  classical
  have hdegree : Q.totalDegree ≤ 2 * p :=
    totalDegree_le_two_mul_of_bidegreeBound p hbound
  rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicHomogenizedCircularChartIForFaces_eq_support_sum _ _ hdegree]
  rw [MvPolynomial.coeff_sum]
  by_cases he : isotropicFaceExponent a p ∈ Q.support
  · rw [Finset.sum_eq_single (isotropicFaceExponent a p)]
    · rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartITermForFaces_coeff_face p a ha _ _ (hbound _ he),
        if_pos rfl]
      ring
    · intro e heQ hne
      rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartITermForFaces_coeff_face p a ha _ _ (hbound _ heQ),
        if_neg hne]
    · intro hnot
      exact (hnot he).elim
  · have hcoeff : MvPolynomial.coeff (isotropicFaceExponent a p) Q = 0 := by
      rwa [← MvPolynomial.notMem_support_iff]
    rw [hcoeff, mul_zero]
    apply Finset.sum_eq_zero
    intro e heQ
    rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartITermForFaces_coeff_face p a ha _ _ (hbound _ heQ),
      if_neg]
    intro heq
    subst e
    exact he heQ

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicHomogenizedCircularChartJForFaces_coeff_face
    (Q : ComplexPlanePoly) (p b : ℕ) (hb : b ≤ p) (hbound : BidegreeBound p Q) :
    MvPolynomial.coeff (isotropicFaceExponent b (p - b))
        (bundle_Esgk_CircularTangentIsotropicFaces_isotropicHomogenizedCircularChartJForFaces (2 * p) Q) =
      (2 : ℂ) ^ p * (-Complex.I) ^ b *
        MvPolynomial.coeff (isotropicFaceExponent p b) Q := by
  classical
  have hdegree : Q.totalDegree ≤ 2 * p :=
    totalDegree_le_two_mul_of_bidegreeBound p hbound
  rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicHomogenizedCircularChartJForFaces_eq_support_sum _ _ hdegree]
  rw [MvPolynomial.coeff_sum]
  by_cases he : isotropicFaceExponent p b ∈ Q.support
  · rw [Finset.sum_eq_single (isotropicFaceExponent p b)]
    · rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartJTermForFaces_coeff_face p b hb _ _ (hbound _ he),
        if_pos rfl]
      ring
    · intro e heQ hne
      rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartJTermForFaces_coeff_face p b hb _ _ (hbound _ heQ),
        if_neg hne]
    · intro hnot
      exact (hnot he).elim
  · have hcoeff : MvPolynomial.coeff (isotropicFaceExponent p b) Q = 0 := by
      rwa [← MvPolynomial.notMem_support_iff]
    rw [hcoeff, mul_zero]
    apply Finset.sum_eq_zero
    intro e heQ
    rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartJTermForFaces_coeff_face p b hb _ _ (hbound _ heQ),
      if_neg]
    intro heq
    subst e
    exact he heQ


theorem circularITangentPolynomial_coeff_eq_isotropic_second_face
    {G : PlanePoly} {p a : ℕ} (hmax : IsMaximallyCircular G)
    (hdegree : G.totalDegree = 2 * p)
    (hbound : BidegreeBound p
      (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)))
    (ha : a ≤ p) :
    (circularITangentPolynomial G).coeff a =
      (2 : ℂ) ^ p * Complex.I ^ a *
        MvPolynomial.coeff (isotropicFaceExponent a p)
          (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)) := by
  have hlocal : planeCircularLocalOrderI G = p := by
    have hI := hmax.1
    omega
  rw [circularITangentPolynomial, hlocal,
    circularChartDehomogenization_homogeneousComponent_coeff _ p a ha,
    hdegree, inline_Esgk_CircularTangentIsotropicFaces__projectiveCircularChartI_planeHomogenization_eq_isotropicForFaces]
  exact inline_Esgk_CircularTangentIsotropicFaces__isotropicHomogenizedCircularChartIForFaces_coeff_face _ p a ha hbound


theorem circularJTangentPolynomial_coeff_eq_isotropic_first_face
    {G : PlanePoly} {p b : ℕ} (hmax : IsMaximallyCircular G)
    (hdegree : G.totalDegree = 2 * p)
    (hbound : BidegreeBound p
      (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)))
    (hb : b ≤ p) :
    (circularJTangentPolynomial G).coeff b =
      (2 : ℂ) ^ p * (-Complex.I) ^ b *
        MvPolynomial.coeff (isotropicFaceExponent p b)
          (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)) := by
  have hlocal : planeCircularLocalOrderJ G = p := by
    have hJ := hmax.2
    omega
  rw [circularJTangentPolynomial, hlocal,
    circularChartDehomogenization_homogeneousComponent_coeff _ p b hb,
    hdegree, inline_Esgk_CircularTangentIsotropicFaces__projectiveCircularChartJ_planeHomogenization_eq_isotropicForFaces]
  exact inline_Esgk_CircularTangentIsotropicFaces__isotropicHomogenizedCircularChartJForFaces_coeff_face _ p b hb hbound


private theorem inline_Esgk_CircularTangentIsotropicFaces__coeff_coeff_bivariateAsSecondVariablePolynomial
    (Q : ComplexPlanePoly) (a b : ℕ) :
    ((bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsSecondVariablePolynomial Q).coeff b).coeff a =
      MvPolynomial.coeff (isotropicFaceExponent a b) Q := by
  induction Q using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp [hP, hQ]
  | monomial e c =>
      rw [bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsSecondVariablePolynomial, MvPolynomial.eval₂Hom_monomial]
      simp [Finsupp.prod_fintype, Fin.prod_univ_two, MvPolynomial.coeff_monomial]
      rw [← map_pow, Polynomial.coeff_C_mul_X_pow]
      by_cases hzero : e 0 = a
      · subst a
        by_cases hone : e 1 = b
        · subst b
          simp [inline_Esgk_CircularTangentIsotropicFaces__eq_isotropicFaceExponent_iff]
        · simp [hone, Ne.symm hone, inline_Esgk_CircularTangentIsotropicFaces__eq_isotropicFaceExponent_iff]
      · have hzero' : a ≠ e 0 := Ne.symm hzero
        by_cases hone : e 1 = b
        · subst b
          simp [hzero, hzero', inline_Esgk_CircularTangentIsotropicFaces__eq_isotropicFaceExponent_iff]
        · simp [hzero, hone, Ne.symm hone,
            inline_Esgk_CircularTangentIsotropicFaces__eq_isotropicFaceExponent_iff]

private theorem inline_Esgk_CircularTangentIsotropicFaces__coeff_coeff_bivariateAsFirstVariablePolynomial
    (Q : ComplexPlanePoly) (a b : ℕ) :
    ((bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsFirstVariablePolynomial Q).coeff a).coeff b =
      MvPolynomial.coeff (isotropicFaceExponent a b) Q := by
  induction Q using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp [hP, hQ]
  | monomial e c =>
      rw [bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsFirstVariablePolynomial, MvPolynomial.eval₂Hom_monomial]
      simp [Finsupp.prod_fintype, Fin.prod_univ_two, MvPolynomial.coeff_monomial]
      rw [mul_comm (Polynomial.X ^ e 0), ← map_pow,
        Polynomial.coeff_C_mul_X_pow]
      by_cases hzero : e 0 = a
      · subst a
        by_cases hone : e 1 = b
        · subst b
          simp [inline_Esgk_CircularTangentIsotropicFaces__eq_isotropicFaceExponent_iff]
        · simp [hone, Ne.symm hone, inline_Esgk_CircularTangentIsotropicFaces__eq_isotropicFaceExponent_iff]
      · have hzero' : a ≠ e 0 := Ne.symm hzero
        by_cases hone : e 1 = b
        · subst b
          simp [hzero, hzero', inline_Esgk_CircularTangentIsotropicFaces__eq_isotropicFaceExponent_iff]
        · simp [hzero, hzero', hone,
            inline_Esgk_CircularTangentIsotropicFaces__eq_isotropicFaceExponent_iff]


@[simp]
theorem isotropicSecondFacePolynomial_coeff (p : ℕ) (Q : ComplexPlanePoly) (a : ℕ) :
    (isotropicSecondFacePolynomial p Q).coeff a =
      MvPolynomial.coeff (isotropicFaceExponent a p) Q := by
  exact inline_Esgk_CircularTangentIsotropicFaces__coeff_coeff_bivariateAsSecondVariablePolynomial Q a p

@[simp]
theorem isotropicFirstFacePolynomial_coeff (p : ℕ) (Q : ComplexPlanePoly) (b : ℕ) :
    (isotropicFirstFacePolynomial p Q).coeff b =
      MvPolynomial.coeff (isotropicFaceExponent p b) Q := by
  exact inline_Esgk_CircularTangentIsotropicFaces__coeff_coeff_bivariateAsFirstVariablePolynomial Q p b

private theorem inline_Esgk_CircularTangentIsotropicFaces__polynomial_coeff_comp_X_add_C_of_natDegree_le
    {R : Type*} [CommSemiring R] [Nontrivial R]
    (P : Polynomial R) (r : R) {p : ℕ} (hdegree : P.natDegree ≤ p) :
    (P.comp (Polynomial.X + Polynomial.C r)).coeff p = P.coeff p := by
  rw [← Polynomial.taylor_apply]
  by_cases hdeg : P.natDegree = p
  · subst p
    rw [Polynomial.coeff_taylor_natDegree, Polynomial.coeff_natDegree]
  · have hlt : P.natDegree < p := lt_of_le_of_ne hdegree hdeg
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    simpa using hlt

private theorem inline_Esgk_CircularTangentIsotropicFaces__polynomial_coeff_comp_X_sub_C_of_natDegree_le
    {R : Type*} [CommRing R] [Nontrivial R]
    (P : Polynomial R) (r : R) {p : ℕ} (hdegree : P.natDegree ≤ p) :
    (P.comp (Polynomial.X - Polynomial.C r)).coeff p = P.coeff p := by
  simpa [sub_eq_add_neg] using
    inline_Esgk_CircularTangentIsotropicFaces__polynomial_coeff_comp_X_add_C_of_natDegree_le P (-r) hdegree


private theorem inline_Esgk_CircularTangentIsotropicFaces__bivariateAsSecondVariablePolynomial_isotropicTranslation
    (c : ℂ) (Q : ComplexPlanePoly) :
    bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsSecondVariablePolynomial (isotropicTranslation c Q) =
      bundle_Esgk_CircularTangentIsotropicFaces_secondVariableIteratedTranslation c (bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsSecondVariablePolynomial Q) := by
  change
    ((bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsSecondVariablePolynomial.comp (isotropicTranslation c)) Q) =
      (((bundle_Esgk_CircularTangentIsotropicFaces_secondVariableIteratedTranslation c).comp
        bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsSecondVariablePolynomial) Q)
  apply RingHom.congr_fun
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsSecondVariablePolynomial, isotropicTranslation,
      bundle_Esgk_CircularTangentIsotropicFaces_secondVariableIteratedTranslation, bundle_Esgk_CircularTangentIsotropicFaces_polynomialTranslation]
  · intro i
    fin_cases i <;>
      simp [bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsSecondVariablePolynomial, isotropicTranslation,
        bundle_Esgk_CircularTangentIsotropicFaces_secondVariableIteratedTranslation, bundle_Esgk_CircularTangentIsotropicFaces_polynomialTranslation]

private theorem inline_Esgk_CircularTangentIsotropicFaces__bivariateAsFirstVariablePolynomial_isotropicTranslation
    (c : ℂ) (Q : ComplexPlanePoly) :
    bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsFirstVariablePolynomial (isotropicTranslation c Q) =
      bundle_Esgk_CircularTangentIsotropicFaces_firstVariableIteratedTranslation c (bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsFirstVariablePolynomial Q) := by
  change
    ((bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsFirstVariablePolynomial.comp (isotropicTranslation c)) Q) =
      (((bundle_Esgk_CircularTangentIsotropicFaces_firstVariableIteratedTranslation c).comp
        bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsFirstVariablePolynomial) Q)
  apply RingHom.congr_fun
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsFirstVariablePolynomial, isotropicTranslation,
      bundle_Esgk_CircularTangentIsotropicFaces_firstVariableIteratedTranslation, bundle_Esgk_CircularTangentIsotropicFaces_polynomialTranslation]
  · intro i
    fin_cases i <;>
      simp [bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsFirstVariablePolynomial, isotropicTranslation,
        bundle_Esgk_CircularTangentIsotropicFaces_firstVariableIteratedTranslation, bundle_Esgk_CircularTangentIsotropicFaces_polynomialTranslation]

private theorem inline_Esgk_CircularTangentIsotropicFaces__bivariateAsSecondVariablePolynomial_natDegree_le
    {Q : ComplexPlanePoly} {p : ℕ} (hbound : BidegreeBound p Q) :
    (bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsSecondVariablePolynomial Q).natDegree ≤ p := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro b hb
  ext a
  rw [Polynomial.coeff_zero, inline_Esgk_CircularTangentIsotropicFaces__coeff_coeff_bivariateAsSecondVariablePolynomial]
  rw [← MvPolynomial.notMem_support_iff]
  intro he
  have hle := (hbound _ he).2
  simp only [isotropicFaceExponent_one] at hle
  exact (not_le_of_gt hb) hle

private theorem inline_Esgk_CircularTangentIsotropicFaces__bivariateAsFirstVariablePolynomial_natDegree_le
    {Q : ComplexPlanePoly} {p : ℕ} (hbound : BidegreeBound p Q) :
    (bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsFirstVariablePolynomial Q).natDegree ≤ p := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro a ha
  ext b
  rw [Polynomial.coeff_zero, inline_Esgk_CircularTangentIsotropicFaces__coeff_coeff_bivariateAsFirstVariablePolynomial]
  rw [← MvPolynomial.notMem_support_iff]
  intro he
  have hle := (hbound _ he).1
  simp only [isotropicFaceExponent_zero] at hle
  exact (not_le_of_gt ha) hle


theorem isotropicSecondFacePolynomial_isotropicTranslation
    (c : ℂ) (p : ℕ) {Q : ComplexPlanePoly} (hbound : BidegreeBound p Q) :
    isotropicSecondFacePolynomial p (isotropicTranslation c Q) =
      (isotropicSecondFacePolynomial p Q).comp
        (Polynomial.X - Polynomial.C c) := by
  rw [isotropicSecondFacePolynomial,
    inline_Esgk_CircularTangentIsotropicFaces__bivariateAsSecondVariablePolynomial_isotropicTranslation]
  let R := bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsSecondVariablePolynomial Q
  let S := Polynomial.map (bundle_Esgk_CircularTangentIsotropicFaces_polynomialTranslation c) R
  have hR : R.natDegree ≤ p := inline_Esgk_CircularTangentIsotropicFaces__bivariateAsSecondVariablePolynomial_natDegree_le hbound
  have hS : S.natDegree ≤ p := Polynomial.natDegree_map_le.trans hR
  change
    (S.comp (Polynomial.X - Polynomial.C (Polynomial.C (star c)))).coeff p = _
  rw [inline_Esgk_CircularTangentIsotropicFaces__polynomial_coeff_comp_X_sub_C_of_natDegree_le S _ hS]
  simp [S, R, isotropicSecondFacePolynomial, bundle_Esgk_CircularTangentIsotropicFaces_polynomialTranslation]


theorem isotropicFirstFacePolynomial_isotropicTranslation
    (c : ℂ) (p : ℕ) {Q : ComplexPlanePoly} (hbound : BidegreeBound p Q) :
    isotropicFirstFacePolynomial p (isotropicTranslation c Q) =
      (isotropicFirstFacePolynomial p Q).comp
        (Polynomial.X - Polynomial.C (star c)) := by
  rw [isotropicFirstFacePolynomial,
    inline_Esgk_CircularTangentIsotropicFaces__bivariateAsFirstVariablePolynomial_isotropicTranslation]
  let R := bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsFirstVariablePolynomial Q
  let S := Polynomial.map (bundle_Esgk_CircularTangentIsotropicFaces_polynomialTranslation (star c)) R
  have hR : R.natDegree ≤ p := inline_Esgk_CircularTangentIsotropicFaces__bivariateAsFirstVariablePolynomial_natDegree_le hbound
  have hS : S.natDegree ≤ p := Polynomial.natDegree_map_le.trans hR
  change
    (S.comp (Polynomial.X - Polynomial.C (Polynomial.C c))).coeff p = _
  rw [inline_Esgk_CircularTangentIsotropicFaces__polynomial_coeff_comp_X_sub_C_of_natDegree_le S _ hS]
  simp [S, R, isotropicFirstFacePolynomial, bundle_Esgk_CircularTangentIsotropicFaces_polynomialTranslation]

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicSecondFacePolynomial_natDegree_le
    {Q : ComplexPlanePoly} {p : ℕ} (hbound : BidegreeBound p Q) :
    (isotropicSecondFacePolynomial p Q).natDegree ≤ p := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro a ha
  rw [isotropicSecondFacePolynomial_coeff]
  rw [← MvPolynomial.notMem_support_iff]
  intro he
  have hle := (hbound _ he).1
  simp only [isotropicFaceExponent_zero] at hle
  exact (not_le_of_gt ha) hle

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicFirstFacePolynomial_natDegree_le
    {Q : ComplexPlanePoly} {p : ℕ} (hbound : BidegreeBound p Q) :
    (isotropicFirstFacePolynomial p Q).natDegree ≤ p := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro b hb
  rw [isotropicFirstFacePolynomial_coeff]
  rw [← MvPolynomial.notMem_support_iff]
  intro he
  have hle := (hbound _ he).2
  simp only [isotropicFaceExponent_one] at hle
  exact (not_le_of_gt hb) hle


theorem circularITangentPolynomial_eq_isotropicSecondFace
    {G : PlanePoly} {p : ℕ} (hmax : IsMaximallyCircular G)
    (hdegree : G.totalDegree = 2 * p)
    (hbound : BidegreeBound p
      (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G))) :
    circularITangentPolynomial G =
      Polynomial.C ((2 : ℂ) ^ p) *
        (isotropicSecondFacePolynomial p
          (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G))).comp
            (Polynomial.C Complex.I * Polynomial.X) := by
  let Q := planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)
  have hlocal : planeCircularLocalOrderI G = p := by
    have hI := hmax.1
    omega
  have hTdegree : (circularITangentPolynomial G).natDegree ≤ p := by
    rw [circularITangentPolynomial, hlocal]
    exact circularChartDehomogenization_natDegree_le
      (MvPolynomial.homogeneousComponent_isHomogeneous p
        (projectiveCircularChartI (planeHomogenization G.totalDegree G)))
  have hFdegree : (isotropicSecondFacePolynomial p Q).natDegree ≤ p :=
    inline_Esgk_CircularTangentIsotropicFaces__isotropicSecondFacePolynomial_natDegree_le hbound
  ext a
  by_cases ha : a ≤ p
  · rw [circularITangentPolynomial_coeff_eq_isotropic_second_face hmax hdegree hbound ha,
      Polynomial.coeff_C_mul, Polynomial.comp_C_mul_X_coeff,
      isotropicSecondFacePolynomial_coeff]
    ring
  · have hpa : p < a := lt_of_not_ge ha
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hTdegree.trans_lt hpa),
      Polynomial.coeff_C_mul, Polynomial.comp_C_mul_X_coeff,
      Polynomial.coeff_eq_zero_of_natDegree_lt (hFdegree.trans_lt hpa)]
    simp


theorem circularJTangentPolynomial_eq_isotropicFirstFace
    {G : PlanePoly} {p : ℕ} (hmax : IsMaximallyCircular G)
    (hdegree : G.totalDegree = 2 * p)
    (hbound : BidegreeBound p
      (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G))) :
    circularJTangentPolynomial G =
      Polynomial.C ((2 : ℂ) ^ p) *
        (isotropicFirstFacePolynomial p
          (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G))).comp
            (Polynomial.C (-Complex.I) * Polynomial.X) := by
  let Q := planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)
  have hlocal : planeCircularLocalOrderJ G = p := by
    have hJ := hmax.2
    omega
  have hTdegree : (circularJTangentPolynomial G).natDegree ≤ p := by
    rw [circularJTangentPolynomial, hlocal]
    exact circularChartDehomogenization_natDegree_le
      (MvPolynomial.homogeneousComponent_isHomogeneous p
        (projectiveCircularChartJ (planeHomogenization G.totalDegree G)))
  have hFdegree : (isotropicFirstFacePolynomial p Q).natDegree ≤ p :=
    inline_Esgk_CircularTangentIsotropicFaces__isotropicFirstFacePolynomial_natDegree_le hbound
  ext b
  by_cases hb : b ≤ p
  · rw [circularJTangentPolynomial_coeff_eq_isotropic_first_face hmax hdegree hbound hb,
      Polynomial.coeff_C_mul, Polynomial.comp_C_mul_X_coeff,
      isotropicFirstFacePolynomial_coeff]
    ring
  · have hpb : p < b := lt_of_not_ge hb
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hTdegree.trans_lt hpb),
      Polynomial.coeff_C_mul, Polynomial.comp_C_mul_X_coeff,
      Polynomial.coeff_eq_zero_of_natDegree_lt (hFdegree.trans_lt hpb)]
    simp

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicTranslation_neg_eq_inverseIsotropicTranslation (c : ℂ) :
    isotropicTranslation (-c) = inverseIsotropicTranslation c := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro i
    fin_cases i <;>
      simp [isotropicTranslation, inverseIsotropicTranslation]

private theorem inline_Esgk_CircularTangentIsotropicFaces__bidegreeBound_of_isotropicTranslation
    (c : ℂ) (p : ℕ) {Q : ComplexPlanePoly}
    (hbound : BidegreeBound p (isotropicTranslation c Q)) :
    BidegreeBound p Q := by
  have hneg := bidegreeBound_isotropicTranslation (-c) p hbound
  rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicTranslation_neg_eq_inverseIsotropicTranslation] at hneg
  have hinv : inverseIsotropicTranslation c (isotropicTranslation c Q) = Q := by
    simpa [RingHom.comp_apply] using
      RingHom.congr_fun (inverseIsotropicTranslation_comp_isotropicTranslation c) Q
  rw [hinv] at hneg
  exact hneg


theorem circularITangentPolynomial_comp_centered_coeff_eq_isotropic_second_face
    {G : PlanePoly} {p a : ℕ} (c : ℂ) (hmax : IsMaximallyCircular G)
    (hdegree : G.totalDegree = 2 * p)
    (hbound : BidegreeBound p
      (isotropicTranslationEquiv c
        (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)))) :
    ((circularITangentPolynomial G).comp
      (Polynomial.X + Polynomial.C (Complex.I * c))).coeff a =
        (2 : ℂ) ^ p * Complex.I ^ a *
          MvPolynomial.coeff (isotropicFaceExponent a p)
            (isotropicTranslationEquiv c
              (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G))) := by
  let Q := planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)
  let Qc := isotropicTranslationEquiv c Q
  have hboundQ : BidegreeBound p Q := by
    apply inline_Esgk_CircularTangentIsotropicFaces__bidegreeBound_of_isotropicTranslation c p
    simpa [Q, Qc] using hbound
  have hface : isotropicSecondFacePolynomial p Qc =
      (isotropicSecondFacePolynomial p Q).comp
        (Polynomial.X - Polynomial.C c) := by
    simpa [Qc, Q] using isotropicSecondFacePolynomial_isotropicTranslation c p hboundQ
  have hbase := circularITangentPolynomial_eq_isotropicSecondFace hmax hdegree hboundQ
  have hpoly :
      (circularITangentPolynomial G).comp
          (Polynomial.X + Polynomial.C (Complex.I * c)) =
        Polynomial.C ((2 : ℂ) ^ p) *
          (isotropicSecondFacePolynomial p Qc).comp
            (Polynomial.C Complex.I * Polynomial.X) := by
    rw [hbase]
    simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.comp_assoc]
    rw [hface, Polynomial.comp_assoc]
    congr 2
    simp
    ring_nf
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
    ring
  rw [hpoly, Polynomial.coeff_C_mul, Polynomial.comp_C_mul_X_coeff,
    isotropicSecondFacePolynomial_coeff]
  ring


theorem circularJTangentPolynomial_comp_centered_coeff_eq_isotropic_first_face
    {G : PlanePoly} {p b : ℕ} (c : ℂ) (hmax : IsMaximallyCircular G)
    (hdegree : G.totalDegree = 2 * p)
    (hbound : BidegreeBound p
      (isotropicTranslationEquiv c
        (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)))) :
    ((circularJTangentPolynomial G).comp
      (Polynomial.X + Polynomial.C (-Complex.I * star c))).coeff b =
        (2 : ℂ) ^ p * (-Complex.I) ^ b *
          MvPolynomial.coeff (isotropicFaceExponent p b)
            (isotropicTranslationEquiv c
              (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G))) := by
  let Q := planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)
  let Qc := isotropicTranslationEquiv c Q
  have hboundQ : BidegreeBound p Q := by
    apply inline_Esgk_CircularTangentIsotropicFaces__bidegreeBound_of_isotropicTranslation c p
    simpa [Q, Qc] using hbound
  have hface : isotropicFirstFacePolynomial p Qc =
      (isotropicFirstFacePolynomial p Q).comp
        (Polynomial.X - Polynomial.C (star c)) := by
    simpa [Qc, Q] using isotropicFirstFacePolynomial_isotropicTranslation c p hboundQ
  have hbase := circularJTangentPolynomial_eq_isotropicFirstFace hmax hdegree hboundQ
  have hpoly :
      (circularJTangentPolynomial G).comp
          (Polynomial.X + Polynomial.C (-Complex.I * star c)) =
        Polynomial.C ((2 : ℂ) ^ p) *
          (isotropicFirstFacePolynomial p Qc).comp
            (Polynomial.C (-Complex.I) * Polynomial.X) := by
    rw [hbase]
    simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.comp_assoc]
    rw [hface, Polynomial.comp_assoc]
    congr 2
    simp
    ring_nf
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
    ring
  rw [hpoly, Polynomial.coeff_C_mul, Polynomial.comp_C_mul_X_coeff,
    isotropicFirstFacePolynomial_coeff]
  ring

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open EuclideanGeometry PachDeZeeuw


theorem exists_moved_point_of_ne_one
    (g : PachDeZeeuw.Algebraic.Point2 ≃ᵢ PachDeZeeuw.Algebraic.Point2) (hne : g ≠ 1) :
    ∃ x : PachDeZeeuw.Algebraic.Point2, g x ≠ x := by
  by_contra hnone
  apply hne
  apply IsometryEquiv.ext
  intro x
  by_contra hx
  exact hnone ⟨x, hx⟩

 
theorem exists_moved_point_of_not_isDirect
    (g : PachDeZeeuw.Algebraic.Point2 ≃ᵢ PachDeZeeuw.Algebraic.Point2) (hreversing : ¬ IsDirect g) :
    ∃ x : PachDeZeeuw.Algebraic.Point2, g x ≠ x :=
  exists_moved_point_of_ne_one g
    (isometryEquiv_ne_one_of_not_isDirect hreversing)

 
theorem perpendicularBisectorDirection_ne_zero
    {x z : PachDeZeeuw.Algebraic.Point2} (hxz : x ≠ z) :
    perpendicularBisectorDirection x z ≠ 0 := by
  intro hzero
  apply hxz
  ext i
  fin_cases i
  · have hcoord := congrArg (fun w : PachDeZeeuw.Algebraic.Point2 ↦ w 1) hzero
    simp [perpendicularBisectorDirection] at hcoord
    simpa using (sub_eq_zero.mp hcoord).symm
  · have hcoord := congrArg (fun w : PachDeZeeuw.Algebraic.Point2 ↦ w 0) hzero
    simp [perpendicularBisectorDirection] at hcoord
    simpa using sub_eq_zero.mp hcoord


theorem CurveSymmetries.affineLine_not_subset
    {d : ℕ} {C : Set CurveSymmetries.Point2}
    (hcurve : CurveSymmetries.IsIrreducibleCurve d C)
    (hnot : ¬ CurveSymmetries.IsLineOrCircle C)
    {x v : CurveSymmetries.Point2} (hv : v ≠ 0) :
    ¬ PachDeZeeuw.Algebraic.PlaneCurveZeroSet
        (affineLinePolynomial x v) ⊆ C := by
  intro hsubset
  obtain ⟨p, _hp0, hpirreducible, hC, hpdivides⟩ :=
    CurveSymmetries.dvd_affineLinePolynomial_of_translationOrbit
      hcurve hv (fun n ↦ hsubset (by
        change MvPolynomial.eval
            (fun i ↦ (x + (n : ℝ) • v) i)
            (affineLinePolynomial x v) = 0
        rw [affineLinePolynomial_eval]
        change v 1 * (x 0 + (n : ℝ) * v 0 - x 0) -
          v 0 * (x 1 + (n : ℝ) * v 1 - x 1) = 0
        ring))
  have hlineIrreducible : Irreducible (affineLinePolynomial x v) :=
    affineLinePolynomial_irreducible hv
  have hassociated : Associated p (affineLinePolynomial x v) :=
    hpirreducible.associated_of_dvd hlineIrreducible hpdivides
  have hzeroSets :
      PachDeZeeuw.Algebraic.PlaneCurveZeroSet p =
        PachDeZeeuw.Algebraic.PlaneCurveZeroSet
          (affineLinePolynomial x v) :=
    zeroSet_eq_of_associated hassociated
  have hcarrierLine : C =
      {z : CurveSymmetries.Point2 |
        v 1 * z 0 + (-v 0) * z 1 = v 1 * x 0 - v 0 * x 1} := by
    calc
      C = CurveSymmetries.PlaneCurveZeroSet p := hC
      _ = PachDeZeeuw.Algebraic.PlaneCurveZeroSet p := by rfl
      _ = PachDeZeeuw.Algebraic.PlaneCurveZeroSet
          (affineLinePolynomial x v) := hzeroSets
      _ = {z : CurveSymmetries.Point2 |
          v 1 * z 0 + (-v 0) * z 1 =
            v 1 * x 0 - v 0 * x 1} :=
        affineLinePolynomial_zeroSet_eq_line x v
  apply hnot
  exact Or.inl ⟨v 1, -v 0, v 1 * x 0 - v 0 * x 1,
    affineLinePolynomial_direction_ne_zero hv, hcarrierLine⟩


theorem fixedPoint_mem_perpendicularBisectorLine
    (g : PachDeZeeuw.Algebraic.Point2 ≃ᵢ PachDeZeeuw.Algebraic.Point2) {x y : PachDeZeeuw.Algebraic.Point2}
    (hy : g y = y) :
    y ∈ PachDeZeeuw.Algebraic.PlaneCurveZeroSet
      (affineLinePolynomial
        (perpendicularBisectorBase x (g x))
        (perpendicularBisectorDirection x (g x))) := by
  have hdist : dist y x = dist y (g x) := by
    calc
      dist y x = dist (g y) (g x) := (g.dist_eq y x).symm
      _ = dist y (g x) := by rw [hy]
  have hsquare := congrArg (fun r : ℝ ↦ r ^ 2) hdist
  change dist y x ^ 2 = dist y (g x) ^ 2 at hsquare
  rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq,
    Fin.sum_univ_two, Fin.sum_univ_two] at hsquare
  simp only [Real.dist_eq, sq_abs] at hsquare
  rw [PachDeZeeuw.Algebraic.mem_PlaneCurveZeroSet,
    affineLinePolynomial_eval]
  simp only [perpendicularBisectorBase, perpendicularBisectorDirection,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  nlinarith

end Esgk

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 as described in the repository LICENSE.
-/


namespace Esgk

open EuclideanGeometry
open PachDeZeeuw (PreparedBipartiteInput Point4)
open PachDeZeeuw.Algebraic (PlaneCurveZeroSet SingularPointSet)


theorem endpoints_not_mem_canonicalAxis_and_nonsingular_of_not_mem_deletedLabel
    {d : ℕ} (X : PreparedBipartiteInput d)
    (axisAnchors : Finset X.P₁) (Γ : Finset (X.P₁ × X.P₁))
    {ij : X.P₁ × X.P₁}
    (hij : ij ∉ selfCurveDeletedLabels X
      (selfCurveExceptionalAnchors X axisAnchors) Γ) :
    ((ij.1 ∉ axisAnchors ∧
        (ij.1 : PachDeZeeuw.Algebraic.Point2) ∉ SingularPointSet (preparedSecondCurvePolynomial X)) ∧
      (ij.2 ∉ axisAnchors ∧
        (ij.2 : PachDeZeeuw.Algebraic.Point2) ∉ SingularPointSet (preparedSecondCurvePolynomial X))) := by
  classical
  obtain ⟨hfirst, hsecond, _⟩ :=
    anchors_not_mem_of_label_not_mem_selfCurveDeletedLabels hij
  exact ⟨⟨by
      intro hp
      exact hfirst ((mem_selfCurveExceptionalAnchors X _ _).2 (Or.inr hp)),
    not_mem_singularPointSet_of_not_mem_selfCurveExceptionalAnchors
      X axisAnchors ij.1 hfirst⟩,
    ⟨by
      intro hp
      exact hsecond ((mem_selfCurveExceptionalAnchors X _ _).2 (Or.inr hp)),
      not_mem_singularPointSet_of_not_mem_selfCurveExceptionalAnchors
        X axisAnchors ij.2 hsecond⟩⟩


theorem normalized_nonreflection_of_not_mem_canonicalAxis
    {d : ℕ} (X : PreparedBipartiteInput d)
    (hself : SelfCurvePreparedInput X) (p : X.P₁)
    (hpaxis : p ∉ selfCurveAxisAnchorsFromReflections X
      (selfCurveReversingCarrierSymmetries hself))
    (g : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) (r : ℝ)
    (hgp : g (p : PachDeZeeuw.Algebraic.Point2) = xAxisPoint r) :
    xAxisReflectionPoint '' PlaneCurveZeroSet
        ((preparedSecondCurveIrreducible X).affineIsometryTransport g).polynomial ≠
      PlaneCurveZeroSet
        ((preparedSecondCurveIrreducible X).affineIsometryTransport g).polynomial := by
  let ρ := xAxisReflectionAffineIsometry
  let h := g.trans ρ |>.trans g.symm
  have hcarrier :=
    (preparedSecondCurveIrreducible X).affineIsometry_image_zeroSet_eq g
  intro hreflect
  have hconj : h '' PlaneCurveZeroSet
      (preparedSecondCurveIrreducible X).polynomial =
      PlaneCurveZeroSet (preparedSecondCurveIrreducible X).polynomial := by
    calc
      _ = g.symm '' (xAxisReflectionPoint ''
          (g '' PlaneCurveZeroSet (preparedSecondCurveIrreducible X).polynomial)) := by
        simp only [Set.image_image]
        rfl
      _ = g.symm '' (g '' PlaneCurveZeroSet
          (preparedSecondCurveIrreducible X).polynomial) := by
        rw [hcarrier, hreflect]
      _ = _ := by rw [Set.image_image]; simp
  have hcarrierX : h.toIsometryEquiv '' X.C₂ = X.C₂ := by
    simpa [preparedSecondCurveIrreducible, preparedSecondCurvePolynomial_zeroSet] using hconj
  have hrev : h.toIsometryEquiv ∈ selfCurveReversingCarrierSymmetries hself :=
    (mem_selfCurveReversingCarrierSymmetries hself _).2
      ⟨hcarrierX, by
        exact xAxisReflectionAffineIsometry_not_isDirect_conjugate g⟩
  have hfix : h.toIsometryEquiv (p : PachDeZeeuw.Algebraic.Point2) = (p : PachDeZeeuw.Algebraic.Point2) := by
    change g.symm (ρ (g (p : PachDeZeeuw.Algebraic.Point2))) = (p : PachDeZeeuw.Algebraic.Point2)
    rw [hgp, xAxisReflectionAffineIsometry_fixed_xAxisPoint, ← hgp,
      g.symm_apply_apply]
  exact hpaxis ((mem_selfCurveAxisAnchorsFromReflections X _ p).2 ⟨h.toIsometryEquiv, hrev, hfix⟩)


end Esgk

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


noncomputable section

namespace Esgk

open EuclideanGeometry
open PachDeZeeuw.Algebraic
open IrreduciblePlanePolynomial


private theorem inline_Esgk_TwoPairDistanceCarrierSymmetry__horizontalReflectionAffine_apply (z : PachDeZeeuw.Algebraic.Point2) :
    bundle_Esgk_TwoPairDistanceCarrierSymmetry_horizontalReflectionAffine z = xAxisReflectionPoint z := by
  change (ℝ ∙ xAxisPoint 1).reflection z = xAxisReflectionPoint z
  ext i
  fin_cases i
  · simp [Submodule.reflection_singleton_apply, xAxisPoint, xAxisReflectionPoint,
      PiLp.inner_apply, Fin.sum_univ_two, EuclideanSpace.norm_sq_eq]
    ring
  · simp [Submodule.reflection_singleton_apply, xAxisPoint, xAxisReflectionPoint,
      PiLp.inner_apply, Fin.sum_univ_two, EuclideanSpace.norm_sq_eq]

private theorem inline_Esgk_TwoPairDistanceCarrierSymmetry__horizontalReflectionAffine_xAxis (t : ℝ) :
    bundle_Esgk_TwoPairDistanceCarrierSymmetry_horizontalReflectionAffine (xAxisPoint t) = xAxisPoint t := by
  rw [inline_Esgk_TwoPairDistanceCarrierSymmetry__horizontalReflectionAffine_apply]
  ext i
  fin_cases i
  · simp [xAxisReflectionPoint, xAxisPoint]
  · simp [xAxisReflectionPoint, xAxisPoint]


private theorem inline_Esgk_TwoPairDistanceCarrierSymmetry__targetReflection_apply_b (b e : PachDeZeeuw.Algebraic.Point2) (hbe : b ≠ e) :
    bundle_Esgk_TwoPairDistanceCarrierSymmetry_targetReflection b e hbe b = b := by
  let r : ℝ := dist b e / 2
  have hr : 0 < r := by
    dsimp [r]
    exact div_pos (dist_pos.mpr hbe) (by norm_num)
  have htarget : dist b e = dist (xAxisPoint (-r)) (xAxisPoint r) := by
    rw [dist_xAxisPoint_neg_eq r hr.le]
    dsimp [r]
    ring
  let g : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2 :=
    directAffineIsometryEquivOfSendPair b e (xAxisPoint (-r))
      (xAxisPoint r) hbe htarget
  have hgb : g b = xAxisPoint (-r) := by
    dsimp [g]
    exact directAffineIsometryEquivOfSendPair_apply_a _ _ _ _ _ _
  change (g.trans (bundle_Esgk_TwoPairDistanceCarrierSymmetry_horizontalReflectionAffine.trans g.symm)) b = b
  change g.symm (bundle_Esgk_TwoPairDistanceCarrierSymmetry_horizontalReflectionAffine (g b)) = b
  calc
    g.symm (bundle_Esgk_TwoPairDistanceCarrierSymmetry_horizontalReflectionAffine (g b)) =
        g.symm (bundle_Esgk_TwoPairDistanceCarrierSymmetry_horizontalReflectionAffine (xAxisPoint (-r))) := by rw [hgb]
    _ = g.symm (xAxisPoint (-r)) := by rw [inline_Esgk_TwoPairDistanceCarrierSymmetry__horizontalReflectionAffine_xAxis]
    _ = b := by rw [← hgb, g.symm_apply_apply]

private theorem inline_Esgk_TwoPairDistanceCarrierSymmetry__targetReflection_apply_e (b e : PachDeZeeuw.Algebraic.Point2) (hbe : b ≠ e) :
    bundle_Esgk_TwoPairDistanceCarrierSymmetry_targetReflection b e hbe e = e := by
  let r : ℝ := dist b e / 2
  have hr : 0 < r := by
    dsimp [r]
    exact div_pos (dist_pos.mpr hbe) (by norm_num)
  have htarget : dist b e = dist (xAxisPoint (-r)) (xAxisPoint r) := by
    rw [dist_xAxisPoint_neg_eq r hr.le]
    dsimp [r]
    ring
  let g : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2 :=
    directAffineIsometryEquivOfSendPair b e (xAxisPoint (-r))
      (xAxisPoint r) hbe htarget
  have hge : g e = xAxisPoint r := by
    dsimp [g]
    exact directAffineIsometryEquivOfSendPair_apply_b _ _ _ _ _ _
  change (g.trans (bundle_Esgk_TwoPairDistanceCarrierSymmetry_horizontalReflectionAffine.trans g.symm)) e = e
  change g.symm (bundle_Esgk_TwoPairDistanceCarrierSymmetry_horizontalReflectionAffine (g e)) = e
  calc
    g.symm (bundle_Esgk_TwoPairDistanceCarrierSymmetry_horizontalReflectionAffine (g e)) =
        g.symm (bundle_Esgk_TwoPairDistanceCarrierSymmetry_horizontalReflectionAffine (xAxisPoint r)) := by rw [hge]
    _ = g.symm (xAxisPoint r) := by rw [inline_Esgk_TwoPairDistanceCarrierSymmetry__horizontalReflectionAffine_xAxis]
    _ = e := by rw [← hge, g.symm_apply_apply]

theorem affineIsometry_carrier_eq_of_infinite_image_intersection
    (C : IrreduciblePlanePolynomial ℝ)
    (T : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2)
    (hinf :
      (T '' PlaneCurveZeroSet C.polynomial ∩
        PlaneCurveZeroSet C.polynomial).Infinite) :
    T '' PlaneCurveZeroSet C.polynomial = PlaneCurveZeroSet C.polynomial := by
  have htransport := C.affineIsometry_image_zeroSet_eq T
  have hpolyinf :
      (PlaneCurveZeroSet (C.affineIsometryTransport T).polynomial ∩
        PlaneCurveZeroSet C.polynomial).Infinite := by
    rw [← htransport]
    exact hinf
  have hassoc : Associated (C.affineIsometryTransport T).polynomial C.polynomial :=
    associated_of_infinite_irreducible_zeroSet_intersection
      (C.affineIsometryTransport T).irreducible C.irreducible hpolyinf
  have hzero :
      PlaneCurveZeroSet (C.affineIsometryTransport T).polynomial =
        PlaneCurveZeroSet C.polynomial :=
    zeroSet_eq_of_associated hassoc
  exact htransport.trans hzero

theorem twoPairDistance_branch_of_affine_isometry
    {a c b e x y : PachDeZeeuw.Algebraic.Point2} (hbe : b ≠ e)
    (T : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) (hTa : T a = b) (hTc : T c = e)
    (h₁ : dist x a ^ 2 = dist y b ^ 2)
    (h₂ : dist x c ^ 2 = dist y e ^ 2) :
    y = T x ∨ y = (T.trans (bundle_Esgk_TwoPairDistanceCarrierSymmetry_targetReflection b e hbe)) x := by
  let r : ℝ := dist b e / 2
  have hr : 0 < r := by
    dsimp [r]
    exact div_pos (dist_pos.mpr hbe) (by norm_num)
  have htarget : dist b e = dist (xAxisPoint (-r)) (xAxisPoint r) := by
    rw [dist_xAxisPoint_neg_eq r hr.le]
    dsimp [r]
    ring
  let g : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2 :=
    directAffineIsometryEquivOfSendPair b e (xAxisPoint (-r))
      (xAxisPoint r) hbe htarget
  have hgb : g b = xAxisPoint (-r) := by
    dsimp [g]
    exact directAffineIsometryEquivOfSendPair_apply_a _ _ _ _ _ _
  have hge : g e = xAxisPoint r := by
    dsimp [g]
    exact directAffineIsometryEquivOfSendPair_apply_b _ _ _ _ _ _
  have hleft :
      ((g (T x)) 0 + r) ^ 2 + ((g (T x)) 1) ^ 2 =
        ((g y) 0 + r) ^ 2 + ((g y) 1) ^ 2 := by
    have hsq : dist (g (T x)) (xAxisPoint (-r)) ^ 2 =
        dist (g y) (xAxisPoint (-r)) ^ 2 := by
      calc
        dist (g (T x)) (xAxisPoint (-r)) ^ 2 =
            dist (g (T x)) (g b) ^ 2 := by rw [hgb]
        _ = dist (T x) b ^ 2 := congrArg (fun z : ℝ ↦ z ^ 2) (g.dist_map _ _)
        _ = dist (T x) (T a) ^ 2 := by rw [hTa]
        _ = dist x a ^ 2 := congrArg (fun z : ℝ ↦ z ^ 2) (T.dist_map _ _)
        _ = dist y b ^ 2 := h₁
        _ = dist (g y) (g b) ^ 2 :=
          (congrArg (fun z : ℝ ↦ z ^ 2) (g.dist_map _ _)).symm
        _ = dist (g y) (xAxisPoint (-r)) ^ 2 := by rw [hgb]
    rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq] at hsq
    simpa [xAxisPoint, Fin.sum_univ_two, Real.dist_eq] using hsq
  have hright :
      ((g (T x)) 0 - r) ^ 2 + ((g (T x)) 1) ^ 2 =
        ((g y) 0 - r) ^ 2 + ((g y) 1) ^ 2 := by
    have hsq : dist (g (T x)) (xAxisPoint r) ^ 2 =
        dist (g y) (xAxisPoint r) ^ 2 := by
      calc
        dist (g (T x)) (xAxisPoint r) ^ 2 =
            dist (g (T x)) (g e) ^ 2 := by rw [hge]
        _ = dist (T x) e ^ 2 := congrArg (fun z : ℝ ↦ z ^ 2) (g.dist_map _ _)
        _ = dist (T x) (T c) ^ 2 := by rw [hTc]
        _ = dist x c ^ 2 := congrArg (fun z : ℝ ↦ z ^ 2) (T.dist_map _ _)
        _ = dist y e ^ 2 := h₂
        _ = dist (g y) (g e) ^ 2 :=
          (congrArg (fun z : ℝ ↦ z ^ 2) (g.dist_map _ _)).symm
        _ = dist (g y) (xAxisPoint r) ^ 2 := by rw [hge]
    rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq] at hsq
    simpa [xAxisPoint, Fin.sum_univ_two, Real.dist_eq] using hsq
  have hbranch := twoAnchor_sqDistance_eq_same_or_reflection hr hleft hright
  rcases hbranch with hsame | hreflect
  · left
    apply g.injective
    ext i
    fin_cases i
    · exact hsame.1.symm
    · exact hsame.2.symm
  · right
    apply g.injective
    have hconj : g ((T.trans (bundle_Esgk_TwoPairDistanceCarrierSymmetry_targetReflection b e hbe)) x) =
        bundle_Esgk_TwoPairDistanceCarrierSymmetry_horizontalReflectionAffine (g (T x)) := by
      simp [bundle_Esgk_TwoPairDistanceCarrierSymmetry_targetReflection, g, r]
    rw [hconj]
    rw [inline_Esgk_TwoPairDistanceCarrierSymmetry__horizontalReflectionAffine_apply]
    ext i
    fin_cases i
    · exact hreflect.1.symm
    · simp [xAxisReflectionPoint]
      linarith [hreflect.2]

private theorem inline_Esgk_TwoPairDistanceCarrierSymmetry__twoPairDistance_fst_fiber_finite
    (C : IrreduciblePlanePolynomial ℝ) {a c b e : PachDeZeeuw.Algebraic.Point2}
    (T Tm : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2)
    (hbranch : ∀ z ∈ twoPairDistanceCommonZeroSet C a c b e,
      z.2 = T z.1 ∨ z.2 = Tm z.1) (q : PachDeZeeuw.Algebraic.Point2) :
    (twoPairDistanceCommonZeroSet C a c b e ∩ Prod.fst ⁻¹' {q}).Finite := by
  by_cases hne : (twoPairDistanceCommonZeroSet C a c b e ∩
      Prod.fst ⁻¹' {q}).Nonempty
  · have hsub : twoPairDistanceCommonZeroSet C a c b e ∩
        Prod.fst ⁻¹' {q} ⊆ ({(q, T q), (q, Tm q)} : Set (PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2)) := by
      intro z hz
      have hzq : z.1 = q := hz.2
      rcases hbranch z hz.1 with hsame | hreflect
      · left
        apply Prod.ext hzq
        simpa [hzq] using hsame
      · right
        apply Prod.ext hzq
        simpa [hzq] using hreflect
    exact ((Set.finite_singleton _).insert _).subset hsub
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact Set.finite_empty

private theorem inline_Esgk_TwoPairDistanceCarrierSymmetry__twoPairDistance_fst_image_eq_union
    (C : IrreduciblePlanePolynomial ℝ) {a c b e : PachDeZeeuw.Algebraic.Point2}
    (T Tm : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2)
    (hbranch : ∀ z ∈ twoPairDistanceCommonZeroSet C a c b e,
      z.2 = T z.1 ∨ z.2 = Tm z.1) :
    Prod.fst '' twoPairDistanceCommonZeroSet C a c b e =
      Prod.fst '' {z | z ∈ twoPairDistanceCommonZeroSet C a c b e ∧
        z.2 = T z.1} ∪
      Prod.fst '' {z | z ∈ twoPairDistanceCommonZeroSet C a c b e ∧
        z.2 = Tm z.1} := by
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases hbranch z hz with hsame | hreflect
    · left
      exact ⟨z, ⟨hz, hsame⟩, rfl⟩
    · right
      exact ⟨z, ⟨hz, hreflect⟩, rfl⟩
  · intro hq
    rcases hq with hq | hq
    · rcases hq with ⟨z, hz, rfl⟩
      exact ⟨z, hz.1, rfl⟩
    · rcases hq with ⟨z, hz, rfl⟩
      exact ⟨z, hz.1, rfl⟩

private theorem inline_Esgk_TwoPairDistanceCarrierSymmetry__carrier_eq_of_infinite_graph_branch
    (C : IrreduciblePlanePolynomial ℝ) (T : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2)
    (U : Set (PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2))
    (hproj : (Prod.fst '' U).Infinite)
    (hsource : ∀ z ∈ U, z.1 ∈ PlaneCurveZeroSet C.polynomial)
    (htarget : ∀ z ∈ U, z.2 ∈ PlaneCurveZeroSet C.polynomial)
    (hgraph : ∀ z ∈ U, z.2 = T z.1) :
    T '' PlaneCurveZeroSet C.polynomial = PlaneCurveZeroSet C.polynomial := by
  have himage : (T '' (Prod.fst '' U)).Infinite := hproj.image T.injective.injOn
  have hsub : T '' (Prod.fst '' U) ⊆
      T '' PlaneCurveZeroSet C.polynomial ∩ PlaneCurveZeroSet C.polynomial := by
    rintro w ⟨q, ⟨z, hz, rfl⟩, rfl⟩
    have hzzero := htarget z hz
    rw [hgraph z hz] at hzzero
    exact ⟨⟨z.1, hsource z hz, rfl⟩, hzzero⟩
  exact affineIsometry_carrier_eq_of_infinite_image_intersection C T
    (himage.mono hsub)

private theorem inline_Esgk_TwoPairDistanceCarrierSymmetry__exists_carrier_of_twoPair_branch_data
    (C : IrreduciblePlanePolynomial ℝ) {a c b e : PachDeZeeuw.Algebraic.Point2}
    (T Tm : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2)
    (hTa : T a = b) (hTc : T c = e)
    (hR_b : Tm a = b) (hR_e : Tm c = e)
    (hbranch : ∀ z ∈ twoPairDistanceCommonZeroSet C a c b e,
      z.2 = T z.1 ∨ z.2 = Tm z.1)
    (hinf : (twoPairDistanceCommonZeroSet C a c b e).Infinite) :
    ∃ S : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2,
      S '' PlaneCurveZeroSet C.polynomial = PlaneCurveZeroSet C.polynomial ∧
      S a = b ∧ S c = e := by
  have hfib (q : PachDeZeeuw.Algebraic.Point2) :
      (twoPairDistanceCommonZeroSet C a c b e ∩ Prod.fst ⁻¹' {q}).Finite :=
    inline_Esgk_TwoPairDistanceCarrierSymmetry__twoPairDistance_fst_fiber_finite C T Tm hbranch q
  have hproj :
      (Prod.fst '' twoPairDistanceCommonZeroSet C a c b e).Infinite :=
    infinite_image_of_infinite_finite_fibers hinf hfib
  have hproj_eq := inline_Esgk_TwoPairDistanceCarrierSymmetry__twoPairDistance_fst_image_eq_union C T Tm hbranch
  rcases (Set.infinite_union.mp (hproj_eq ▸ hproj)) with hplus | hminus
  · have hcarrier := inline_Esgk_TwoPairDistanceCarrierSymmetry__carrier_eq_of_infinite_graph_branch C T
      {z | z ∈ twoPairDistanceCommonZeroSet C a c b e ∧ z.2 = T z.1}
      hplus
      (fun z hz => hz.1.1)
      (fun z hz => hz.1.2.1)
      (fun z hz => hz.2)
    exact ⟨T, hcarrier, hTa, hTc⟩
  · have hcarrier := inline_Esgk_TwoPairDistanceCarrierSymmetry__carrier_eq_of_infinite_graph_branch C Tm
      {z | z ∈ twoPairDistanceCommonZeroSet C a c b e ∧ z.2 = Tm z.1}
      hminus
      (fun z hz => hz.1.1)
      (fun z hz => hz.1.2.1)
      (fun z hz => hz.2)
    exact ⟨Tm, hcarrier, hR_b, hR_e⟩

theorem exists_affineIsometry_carrier_symmetry_of_dist_eq_of_infinite_twoPair
    (C : IrreduciblePlanePolynomial ℝ)
    {a c b e : PachDeZeeuw.Algebraic.Point2} (hac : a ≠ c) (hbe : b ≠ e)
    (hdist : dist a c = dist b e)
    (hinf : (twoPairDistanceCommonZeroSet C a c b e).Infinite) :
    ∃ T : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2,
      T '' PlaneCurveZeroSet C.polynomial = PlaneCurveZeroSet C.polynomial ∧
      T a = b ∧ T c = e := by
   
   
  obtain ⟨T, hTa, hTc⟩ : ∃ T : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2, T a = b ∧ T c = e :=
    ⟨directAffineIsometryEquivOfSendPair a c b e hac hdist,
      directAffineIsometryEquivOfSendPair_apply_a _ _ _ _ _ _,
      directAffineIsometryEquivOfSendPair_apply_b _ _ _ _ _ _⟩
  let R : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2 := bundle_Esgk_TwoPairDistanceCarrierSymmetry_targetReflection b e hbe
  let Tm : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2 := T.trans R
  have hR_b : R b = b := by
    exact inline_Esgk_TwoPairDistanceCarrierSymmetry__targetReflection_apply_b b e hbe
  have hR_e : R e = e := by
    exact inline_Esgk_TwoPairDistanceCarrierSymmetry__targetReflection_apply_e b e hbe
  have hbranch (z : PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2) (hz : z ∈ twoPairDistanceCommonZeroSet C a c b e) :
      z.2 = T z.1 ∨ z.2 = Tm z.1 := by
    exact twoPairDistance_branch_of_affine_isometry hbe T hTa hTc hz.2.2.1 hz.2.2.2
  have hTm_a : Tm a = b := by
    dsimp [Tm]
    rw [hTa, hR_b]
  have hTm_c : Tm c = e := by
    dsimp [Tm]
    rw [hTc, hR_e]
  exact inline_Esgk_TwoPairDistanceCarrierSymmetry__exists_carrier_of_twoPair_branch_data C T Tm hTa hTc hTm_a hTm_c hbranch hinf

theorem exists_affineIsometry_carrier_symmetry_of_infinite_intersection_of_nonsingular
    (C : IrreduciblePlanePolynomial ℝ)
    (g₁ g₂ : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) {r₁ r₂ : ℝ}
    (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0)
    (hns₁ :
      xAxisReflectionPoint ''
          PlaneCurveZeroSet (C.affineIsometryTransport g₁).polynomial ≠
        PlaneCurveZeroSet (C.affineIsometryTransport g₁).polynomial)
    (hns₂ :
      xAxisReflectionPoint ''
          PlaneCurveZeroSet (C.affineIsometryTransport g₂).polynomial ≠
        PlaneCurveZeroSet (C.affineIsometryTransport g₂).polynomial)
    (a c b e : PachDeZeeuw.Algebraic.Point2)
    (hg₁a : g₁ a = xAxisPoint (-r₁))
    (hg₁c : g₁ c = xAxisPoint r₁)
    (hg₂b : g₂ b = xAxisPoint (-r₂))
    (hg₂e : g₂ e = xAxisPoint r₂)
    (hinf : (twoPairDistanceCommonZeroSet C a c b e).Infinite)
    (ha : a ∈ PlaneCurveZeroSet C.polynomial)
    (hnonsingular : a ∉ SingularPointSet C.polynomial) :
    ∃ T : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2,
      T '' PlaneCurveZeroSet C.polynomial = PlaneCurveZeroSet C.polynomial ∧
      T a = b ∧ T c = e := by
  have hac : a ≠ c := by
    intro hac
    have heq : xAxisPoint (-r₁) = xAxisPoint r₁ := by
      calc
        xAxisPoint (-r₁) = g₁ a := hg₁a.symm
        _ = g₁ c := by rw [hac]
        _ = xAxisPoint r₁ := hg₁c
    have hcoord := congrArg (fun z : PachDeZeeuw.Algebraic.Point2 => z 0) heq
    have hzero : r₁ = 0 := by
      simp [xAxisPoint] at hcoord
      linarith
    exact hr₁ hzero
  have hbe : b ≠ e := by
    intro hbe
    have heq : xAxisPoint (-r₂) = xAxisPoint r₂ := by
      calc
        xAxisPoint (-r₂) = g₂ b := hg₂b.symm
        _ = g₂ e := by rw [hbe]
        _ = xAxisPoint r₂ := hg₂e
    have hcoord := congrArg (fun z : PachDeZeeuw.Algebraic.Point2 => z 0) heq
    have hzero : r₂ = 0 := by
      simp [xAxisPoint] at hcoord
      linarith
    exact hr₂ hzero
  obtain ⟨x, degreeRight, hxa, hxb, hdist⟩ :=
    C.exists_point_and_comap_basePoint_eq_and_dist_eq_of_infinite_intersection_of_nonsingular
      g₁ g₂ hr₁ hr₂ hns₁ hns₂ a c b e hg₁a hg₁c hg₂b hg₂e hinf ha hnonsingular
  exact exists_affineIsometry_carrier_symmetry_of_dist_eq_of_infinite_twoPair C
    hac hbe hdist hinf

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open MvPolynomial
open PachDeZeeuw.Algebraic


theorem IsMaximallyCircular.centered_isotropic_corner_normal_form_of_tangent_identities
    {G : PlanePoly} {p : ℕ} (hmax : IsMaximallyCircular G) (hG : G ≠ 0)
    (hdegree : G.totalDegree = 2 * p) (hp : 0 < p) (ξ : ℂ)
    (hcenterI :
      (circularITangentPolynomial G).comp
          (Polynomial.X + Polynomial.C (Complex.I * ξ)) =
        Polynomial.C (circularITangentPolynomial G).leadingCoeff * Polynomial.X ^ p)
    (hcenterJ :
      (circularJTangentPolynomial G).comp
          (Polynomial.X + Polynomial.C (-Complex.I * star ξ)) =
        Polynomial.C (star (circularITangentPolynomial G).leadingCoeff) *
          Polynomial.X ^ p) :
    ∃ c : ℂ, ∃ R : BidegreePolynomial ℂ,
      c ≠ 0 ∧
        isotropicTranslationEquiv ξ
            (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)) =
          MvPolynomial.monomial (bivariateCornerExponent p) c + R ∧
        BidegreeBound (p - 1) R := by
  let Q : ComplexPlanePoly :=
    planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)
  have hI : circularITangentPolynomial G ≠ 0 :=
    hmax.circularITangentPolynomial_ne_zero hG
  let Qc : ComplexPlanePoly := isotropicTranslationEquiv ξ Q
  have hboundQ : BidegreeBound p Q := by
    simpa only [Q] using
      hmax.bidegreeBound_planeIsotropicCoordinateEquiv hG p hdegree
  have hbound : BidegreeBound p Qc := by
    simpa only [Qc, isotropicTranslationEquiv_apply] using
      bidegreeBound_isotropicTranslation ξ p hboundQ
  have hrow : ∀ a < p, MvPolynomial.coeff (isotropicFaceExponent a p) Qc = 0 := by
    intro a ha
    have hcenterCoeff :
        ((circularITangentPolynomial G).comp
          (Polynomial.X + Polynomial.C (Complex.I * ξ))).coeff a = 0 := by
      rw [hcenterI, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      simp [ne_of_lt ha]
    have hface :=
      circularITangentPolynomial_comp_centered_coeff_eq_isotropic_second_face
        (G := G) (p := p) (a := a) ξ hmax hdegree hbound
    rw [hcenterCoeff] at hface
    have hscalar : (2 : ℂ) ^ p * Complex.I ^ a ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num))
        (pow_ne_zero _ Complex.I_ne_zero)
    exact (mul_eq_zero.mp hface.symm).resolve_left hscalar
  have hcolumn : ∀ b < p, MvPolynomial.coeff (isotropicFaceExponent p b) Qc = 0 := by
    intro b hb
    have hcenterCoeff :
        ((circularJTangentPolynomial G).comp
          (Polynomial.X + Polynomial.C (-Complex.I * star ξ))).coeff b = 0 := by
      rw [hcenterJ, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      simp [ne_of_lt hb]
    have hface :=
      circularJTangentPolynomial_comp_centered_coeff_eq_isotropic_first_face
        (G := G) (p := p) (b := b) ξ hmax hdegree hbound
    rw [hcenterCoeff] at hface
    have hscalar : (2 : ℂ) ^ p * (-Complex.I) ^ b ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num))
        (pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero))
    exact (mul_eq_zero.mp hface.symm).resolve_left hscalar
  have hcorner : MvPolynomial.coeff (bivariateCornerExponent p) Qc ≠ 0 := by
    have hcenterCoeff :
        ((circularITangentPolynomial G).comp
          (Polynomial.X + Polynomial.C (Complex.I * ξ))).coeff p ≠ 0 := by
      rw [hcenterI, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_self, mul_one]
      exact Polynomial.leadingCoeff_ne_zero.mpr hI
    have hface :=
      circularITangentPolynomial_comp_centered_coeff_eq_isotropic_second_face
        (G := G) (p := p) (a := p) ξ hmax hdegree hbound
    have hproduct :
        (2 : ℂ) ^ p * Complex.I ^ p *
          MvPolynomial.coeff (isotropicFaceExponent p p) Qc ≠ 0 := by
      rw [← hface]
      exact hcenterCoeff
    have hcornerFace : MvPolynomial.coeff (isotropicFaceExponent p p) Qc ≠ 0 :=
      (mul_ne_zero_iff.mp hproduct).2
    simpa only [bivariateCornerExponent, isotropicFaceExponent] using hcornerFace
  have htotal : Qc.totalDegree = 2 * p := by
    apply Nat.le_antisymm (totalDegree_le_two_mul_of_bidegreeBound p hbound)
    have hmem : bivariateCornerExponent p ∈ Qc.support :=
      MvPolynomial.mem_support_iff.mpr hcorner
    have hle := MvPolynomial.le_totalDegree hmem
    simpa [bivariateCornerExponent, Finsupp.degree_eq_sum, Finsupp.sum_fintype,
      Fin.sum_univ_two, two_mul] using hle
  obtain ⟨c, R, hc, hform, hR⟩ :=
    exists_bivariate_corner_normal_form Qc p hp hbound htotal
      (by simpa only [isotropicFaceExponent] using hrow)
      (by simpa only [isotropicFaceExponent] using hcolumn)
  refine ⟨c, R, hc, ?_, hR⟩
  simpa only [Qc, Q] using hform


theorem IsMaximallyCircular.exists_centered_isotropic_corner_normal_form
    {G : PlanePoly} {p : ℕ} (hmax : IsMaximallyCircular G) (hG : G ≠ 0)
    (hdegree : G.totalDegree = 2 * p) (hp : 0 < p)
    (hroots : (circularITangentPolynomial G).roots.toFinset.card = 1) :
    ∃ ξ c : ℂ, ∃ R : BidegreePolynomial ℂ,
      c ≠ 0 ∧
        isotropicTranslationEquiv ξ
            (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)) =
          MvPolynomial.monomial (bivariateCornerExponent p) c + R ∧
        BidegreeBound (p - 1) R := by
  have hI : circularITangentPolynomial G ≠ 0 :=
    hmax.circularITangentPolynomial_ne_zero hG
  have hIdegree : (circularITangentPolynomial G).natDegree = p :=
    hmax.circularITangentPolynomial_natDegree hG hdegree
  obtain ⟨ξ, hcenterI, hcenterJ⟩ :=
    exists_simultaneously_centered_circular_tangent_polynomials hI hIdegree hroots
  obtain ⟨c, R, hc, hform, hR⟩ :=
    hmax.centered_isotropic_corner_normal_form_of_tangent_identities
      hG hdegree hp ξ hcenterI hcenterJ
  exact ⟨ξ, c, R, hc, hform, hR⟩

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open EuclideanGeometry PachDeZeeuw PachDeZeeuw.Algebraic


theorem selfCurveFixedAnchorsFor_card_le_of_mem_reversingCarrierSymmetries
    {d : ℕ} {X : PreparedBipartiteInput d}
    (hself : SelfCurvePreparedInput X)
    (g : CurveSymmetries.Point2 ≃ᵢ CurveSymmetries.Point2)
    (hg : g ∈ selfCurveReversingCarrierSymmetries hself) :
    (selfCurveFixedAnchorsFor X g).card ≤ d := by
  classical
  have hreversing : ¬ IsDirect g :=
    (mem_selfCurveReversingCarrierSymmetries hself g).1 hg |>.2
  obtain ⟨x, hx⟩ := exists_moved_point_of_not_isDirect g hreversing
  let base := perpendicularBisectorBase x (g x)
  let direction := perpendicularBisectorDirection x (g x)
  have hdirection : direction ≠ 0 := by
    exact perpendicularBisectorDirection_ne_zero hx.symm
  let anchorEmbedding : X.P₁ ↪ CurveSymmetries.Point2 :=
    ⟨fun p ↦ (p : CurveSymmetries.Point2), Subtype.val_injective⟩
  let fixedPoints : Finset CurveSymmetries.Point2 :=
    (selfCurveFixedAnchorsFor X g).map anchorEmbedding
  have hnotCarrier :
      ¬ PlaneCurveZeroSet (affineLinePolynomial base direction) ⊆ X.C₂ :=
    CurveSymmetries.affineLine_not_subset
      (preparedSecondCurve_isIrreducibleCurve X)
      (selfCurvePreparedInput_not_isLineOrCircle hself)
      hdirection
  have hnotPolynomial :
      ¬ PlaneCurveZeroSet (affineLinePolynomial base direction) ⊆
        PlaneCurveZeroSet (preparedSecondCurvePolynomial X) := by
    rw [← preparedSecondCurvePolynomial_zeroSet X]
    exact hnotCarrier
  have hbound : fixedPoints.card ≤ d :=
    finite_affineLine_zeroSet_card_le_of_not_subset
      (preparedSecondCurvePolynomial X) base d fixedPoints hdirection
      (preparedSecondCurvePolynomial_totalDegree_le X)
      (by
        intro z hz
        obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hz
        have hpCurve :=
          selfCurveAnchor_mem_preparedSecondCurve_zeroSet hself p
        exact hpCurve)
      (by
        intro z hz
        obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hz
        have hpFixed : g (p : CurveSymmetries.Point2) =
            (p : CurveSymmetries.Point2) :=
          (mem_selfCurveFixedAnchorsFor X g p).1 hp
        exact fixedPoint_mem_perpendicularBisectorLine g hpFixed)
      hnotPolynomial
  simpa [fixedPoints] using hbound


theorem selfCurveCanonicalSymmetryFamilies_deletedLabels_card_le_eight_mul_degree_sq
    {d : ℕ} (X : PreparedBipartiteInput d)
    (hself : SelfCurvePreparedInput X) (hd : 2 ≤ d) :
    (selfCurveDeletedLabels X
      (selfCurveExceptionalAnchors X
        (selfCurveAxisAnchorsFromReflections X
          (selfCurveReversingCarrierSymmetries hself)))
      (selfCurveSymmetryLabels X
        (selfCurveCarrierSymmetries hself))).card ≤
      8 * d ^ 2 * X.P₁.card := by
  exact selfCurveCompleteSymmetryFamily_deletedLabels_card_le_eight_mul_degree_sq
    X hself (selfCurveReversingCarrierSymmetries hself) hd
    (selfCurveReversingCarrierSymmetries_card_le hself)
    (selfCurveFixedAnchorsFor_card_le_of_mem_reversingCarrierSymmetries hself)


end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open PachDeZeeuw.Algebraic (PlaneCurveZeroSet mem_PlaneCurveZeroSet)
open IrreduciblePlanePolynomial

private theorem inline_Esgk_TwoPairDistanceRepeatedAnchors__finite_of_finset_card_bound {α : Type*} (S : Set α) (B : ℕ)
    (hbound : ∀ T : Finset α, (↑T : Set α) ⊆ S → T.card ≤ B) :
    S.Finite := by
  by_contra hinf
  obtain ⟨T, hT, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (B + 1)
  have := hbound T hT
  omega

private theorem inline_Esgk_TwoPairDistanceRepeatedAnchors__carrier_isIrreducibleCurve (C : IrreduciblePlanePolynomial ℝ) :
    CurveSymmetries.IsIrreducibleCurve C.polynomial.totalDegree
      (PlaneCurveZeroSet C.polynomial) :=
  ⟨C.polynomial, C.irreducible.ne_zero, le_rfl, C.irreducible, rfl⟩

private theorem inline_Esgk_TwoPairDistanceRepeatedAnchors__carrier_inter_sphere_finite
    (C : IrreduciblePlanePolynomial ℝ)
    (hnot : ¬ CurveSymmetries.IsLineOrCircle (PlaneCurveZeroSet C.polynomial))
    (a : PachDeZeeuw.Algebraic.Point2) {r : ℝ} (hr : 0 ≤ r) :
    (PlaneCurveZeroSet C.polynomial ∩ Metric.sphere a r).Finite := by
  by_cases hr0 : r = 0
  · subst r
    have hsphere : (Metric.sphere a 0).Finite := by
      simpa using Set.finite_singleton a
    exact hsphere.subset Set.inter_subset_right
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  apply inline_Esgk_TwoPairDistanceRepeatedAnchors__finite_of_finset_card_bound _ (2 * C.polynomial.totalDegree)
  intro T hT
  exact finite_circle_zeroSet_card_le_two_mul_of_not_sphere_subset
    C.polynomial a r C.polynomial.totalDegree T hrpos le_rfl
    (fun z hz ↦ (hT hz).1) (fun z hz ↦ (hT hz).2)
    (CurveSymmetries.sphere_not_subset_of_irreducibleCurve_not_lineOrCircle
      (inline_Esgk_TwoPairDistanceRepeatedAnchors__carrier_isIrreducibleCurve C) hnot a hrpos)

private theorem inline_Esgk_TwoPairDistanceRepeatedAnchors__carrier_inter_line_finite
    (C : IrreduciblePlanePolynomial ℝ)
    (hnot : ¬ CurveSymmetries.IsLineOrCircle (PlaneCurveZeroSet C.polynomial))
    (a v : PachDeZeeuw.Algebraic.Point2) (hv : v ≠ 0) :
    (PlaneCurveZeroSet C.polynomial ∩
      PlaneCurveZeroSet (affineLinePolynomial a v)).Finite := by
  apply inline_Esgk_TwoPairDistanceRepeatedAnchors__finite_of_finset_card_bound _ C.polynomial.totalDegree
  intro T hT
  exact finite_affineLine_zeroSet_card_le_of_not_subset
    C.polynomial a C.polynomial.totalDegree T hv le_rfl
    (fun z hz ↦ (hT hz).1) (fun z hz ↦ (hT hz).2)
    (CurveSymmetries.affineLine_not_subset
      (inline_Esgk_TwoPairDistanceRepeatedAnchors__carrier_isIrreducibleCurve C) hnot hv)

private theorem inline_Esgk_TwoPairDistanceRepeatedAnchors__mem_bisector_of_dist_sq_eq {b e y : PachDeZeeuw.Algebraic.Point2}
    (h : dist y b ^ 2 = dist y e ^ 2) :
    y ∈ PlaneCurveZeroSet (affineLinePolynomial
      (perpendicularBisectorBase b e) (perpendicularBisectorDirection b e)) := by
  rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq,
    Fin.sum_univ_two, Fin.sum_univ_two] at h
  simp only [Real.dist_eq, sq_abs] at h
  rw [mem_PlaneCurveZeroSet, affineLinePolynomial_eval]
  simp only [perpendicularBisectorBase, perpendicularBisectorDirection,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  nlinarith


theorem twoPairDistanceCommonZeroSet_finite_of_source_anchor_repeated
    (C : IrreduciblePlanePolynomial ℝ)
    (hnot : ¬ CurveSymmetries.IsLineOrCircle (PlaneCurveZeroSet C.polynomial))
    (a b e : PachDeZeeuw.Algebraic.Point2) (hbe : b ≠ e) :
    (twoPairDistanceCommonZeroSet C a a b e).Finite := by
  have hline := inline_Esgk_TwoPairDistanceRepeatedAnchors__carrier_inter_line_finite C hnot
    (perpendicularBisectorBase b e) (perpendicularBisectorDirection b e)
    (perpendicularBisectorDirection_ne_zero hbe)
  apply Set.Finite.of_finite_fibers Prod.snd
  · apply hline.subset
    rintro y ⟨z, hz, rfl⟩
    exact ⟨hz.2.1, inline_Esgk_TwoPairDistanceRepeatedAnchors__mem_bisector_of_dist_sq_eq (hz.2.2.1.symm.trans hz.2.2.2)⟩
  · intro y _hy
    have hfiber := (inline_Esgk_TwoPairDistanceRepeatedAnchors__carrier_inter_sphere_finite C hnot a
      (dist_nonneg (x := y) (y := b))).prod (Set.finite_singleton y)
    apply hfiber.subset
    rintro z ⟨hz, hzy⟩
    have hzy' : z.2 = y := hzy
    refine ⟨⟨hz.1, ?_⟩, hzy'⟩
    change dist z.1 a = dist y b
    have hsq := hz.2.2.1
    rw [hzy'] at hsq
    nlinarith [dist_nonneg (x := z.1) (y := a), dist_nonneg (x := y) (y := b)]

 
theorem twoPairDistanceCommonZeroSet_finite_of_target_anchor_repeated
    (C : IrreduciblePlanePolynomial ℝ)
    (hnot : ¬ CurveSymmetries.IsLineOrCircle (PlaneCurveZeroSet C.polynomial))
    (a c b : PachDeZeeuw.Algebraic.Point2) (hac : a ≠ c) :
    (twoPairDistanceCommonZeroSet C a c b b).Finite := by
  have hfinite := twoPairDistanceCommonZeroSet_finite_of_source_anchor_repeated
    C hnot b a c hac
  have himage : (Prod.swap '' twoPairDistanceCommonZeroSet C a c b b).Finite := by
    apply hfinite.subset
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨hz.2.1, hz.1, hz.2.2.1.symm, hz.2.2.2.symm⟩
  exact himage.of_finite_image (Equiv.prodComm PachDeZeeuw.Algebraic.Point2 PachDeZeeuw.Algebraic.Point2).injective.injOn

 
theorem twoPairDistanceCommonZeroSet_finite_of_repeated_anchor
    (C : IrreduciblePlanePolynomial ℝ)
    (hnot : ¬ CurveSymmetries.IsLineOrCircle (PlaneCurveZeroSet C.polynomial))
    (a c b e : PachDeZeeuw.Algebraic.Point2) (hlabels : (a, b) ≠ (c, e))
    (hrepeated : a = c ∨ b = e) :
    (twoPairDistanceCommonZeroSet C a c b e).Finite := by
  rcases hrepeated with hac | hbe
  · subst c
    apply twoPairDistanceCommonZeroSet_finite_of_source_anchor_repeated C hnot
    intro hbe
    exact hlabels (Prod.ext rfl hbe)
  · subst e
    apply twoPairDistanceCommonZeroSet_finite_of_target_anchor_repeated C hnot
    intro hac
    exact hlabels (Prod.ext hac rfl)

end Esgk

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open MvPolynomial
open PachDeZeeuw.Algebraic


private theorem inline_Esgk_MaximallyCircularDegreeTwoCircle__bivariateCornerMonomial_one (c : ℂ) :
    MvPolynomial.monomial (bivariateCornerExponent 1) c =
      MvPolynomial.C c * (MvPolynomial.X 0 * MvPolynomial.X 1) := by
  rw [MvPolynomial.monomial_eq]
  simp [bivariateCornerExponent, Finsupp.prod_fintype, Fin.prod_univ_two]

private theorem inline_Esgk_MaximallyCircularDegreeTwoCircle__bidegreeBound_zero_eq_C (R : BidegreePolynomial ℂ)
    (hR : BidegreeBound 0 R) :
    R = MvPolynomial.C (R.coeff 0) := by
  apply MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
  have hdegree := totalDegree_le_two_mul_of_bidegreeBound 0 hR
  omega

private theorem inline_Esgk_MaximallyCircularDegreeTwoCircle__isotropicTranslationCenter_zw (ξ : ℂ) :
    planeIsotropicCoordinateEquiv.symm
        ((isotropicTranslationEquiv ξ).symm
          (MvPolynomial.X 0 * MvPolynomial.X 1)) =
      realToComplexPlanePolynomial
        (planeSquaredDistancePolynomial (bundle_Esgk_MaximallyCircularDegreeTwoCircle_isotropicTranslationCenter ξ)) := by
  rcases ξ with ⟨a, b⟩
  simp [planeIsotropicCoordinateEquiv_symm_apply, isotropicTranslationEquiv_symm_apply,
    inverseIsotropicTranslation, isotropicToPlaneCoordinates, planeSquaredDistancePolynomial,
    realToComplexPlanePolynomial, bundle_Esgk_MaximallyCircularDegreeTwoCircle_isotropicTranslationCenter]
  have hmk : ({ re := a, im := b } : ℂ) = (a : ℂ) + b * Complex.I := by
    apply Complex.ext <;> simp
  have hstar : (starRingEnd ℂ) ({ re := a, im := b } : ℂ) =
      (a : ℂ) - b * Complex.I := by
    apply Complex.ext <;> simp
  rw [hstar, hmk]
  simp only [map_add, map_sub, map_mul]
  ring_nf
  rw [show (MvPolynomial.C Complex.I : ComplexPlanePoly) ^ 2 = -1 by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]]
  ring

private theorem inline_Esgk_MaximallyCircularDegreeTwoCircle__realToComplex_eq_centered_corner_one
    {G : PachDeZeeuw.Algebraic.PlanePoly} {ξ c : ℂ} {R : BidegreePolynomial ℂ}
    (hform :
      isotropicTranslationEquiv ξ
          (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)) =
        MvPolynomial.monomial (bivariateCornerExponent 1) c + R)
    (hR : BidegreeBound 0 R) :
    realToComplexPlanePolynomial G =
      MvPolynomial.C c * realToComplexPlanePolynomial
          (planeSquaredDistancePolynomial (bundle_Esgk_MaximallyCircularDegreeTwoCircle_isotropicTranslationCenter ξ)) +
        MvPolynomial.C (R.coeff 0) := by
  have hRconst : R = MvPolynomial.C (R.coeff 0) :=
    inline_Esgk_MaximallyCircularDegreeTwoCircle__bidegreeBound_zero_eq_C R hR
  calc
    realToComplexPlanePolynomial G =
        planeIsotropicCoordinateEquiv.symm
          ((isotropicTranslationEquiv ξ).symm
            (isotropicTranslationEquiv ξ
              (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)))) := by
                rw [RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
    _ = planeIsotropicCoordinateEquiv.symm
          ((isotropicTranslationEquiv ξ).symm
            (MvPolynomial.monomial (bivariateCornerExponent 1) c + R)) := by rw [hform]
    _ = planeIsotropicCoordinateEquiv.symm
          ((isotropicTranslationEquiv ξ).symm
            (MvPolynomial.C c * (MvPolynomial.X 0 * MvPolynomial.X 1) +
              MvPolynomial.C (R.coeff 0))) := by
            nth_rewrite 1 [hRconst]
            congr 3
            exact inline_Esgk_MaximallyCircularDegreeTwoCircle__bivariateCornerMonomial_one c
    _ = planeIsotropicCoordinateEquiv.symm
            ((isotropicTranslationEquiv ξ).symm (MvPolynomial.C c)) *
          planeIsotropicCoordinateEquiv.symm
            ((isotropicTranslationEquiv ξ).symm
              (MvPolynomial.X 0 * MvPolynomial.X 1)) +
        planeIsotropicCoordinateEquiv.symm
          ((isotropicTranslationEquiv ξ).symm (MvPolynomial.C (R.coeff 0))) := by
            rw [map_add, map_add, map_mul, map_mul]
    _ = MvPolynomial.C c * realToComplexPlanePolynomial
          (planeSquaredDistancePolynomial (bundle_Esgk_MaximallyCircularDegreeTwoCircle_isotropicTranslationCenter ξ)) +
        MvPolynomial.C (R.coeff 0) := by
          rw [inline_Esgk_MaximallyCircularDegreeTwoCircle__isotropicTranslationCenter_zw]
          simp [planeIsotropicCoordinateEquiv_symm_apply, isotropicTranslationEquiv_symm_apply]

private theorem inline_Esgk_MaximallyCircularDegreeTwoCircle__centered_map_scalar_eq
    {G : PachDeZeeuw.Algebraic.PlanePoly} {ξ c d : ℂ}
    (hmap : realToComplexPlanePolynomial G =
      MvPolynomial.C c * realToComplexPlanePolynomial
          (planeSquaredDistancePolynomial (bundle_Esgk_MaximallyCircularDegreeTwoCircle_isotropicTranslationCenter ξ)) +
        MvPolynomial.C d) :
    Complex.ofReal (G.coeff (Finsupp.single 0 2)) = c := by
  have hdistcoeff :
      (planeSquaredDistancePolynomial (bundle_Esgk_MaximallyCircularDegreeTwoCircle_isotropicTranslationCenter ξ)).coeff
          (Finsupp.single (0 : Fin 2) 2) = 1 := by
    have htop := congrArg
      (MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 2))
      (homogeneousComponent_two_planeSquaredDistancePolynomial
        (bundle_Esgk_MaximallyCircularDegreeTwoCircle_isotropicTranslationCenter ξ))
    rw [MvPolynomial.coeff_homogeneousComponent] at htop
    have hsingle : Finsupp.single (1 : Fin 2) 2 ≠ Finsupp.single 0 2 := by
      intro h
      have hzero := DFunLike.congr_fun h 0
      simp at hzero
    simpa [planeRadialQuadratic, MvPolynomial.coeff_add,
      MvPolynomial.coeff_X_pow, hsingle] using htop
  have hcoeff := congrArg
    (MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 2)) hmap
  change MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 2)
      (MvPolynomial.map Complex.ofRealHom G) =
    MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 2)
      (MvPolynomial.C c * MvPolynomial.map Complex.ofRealHom
        (planeSquaredDistancePolynomial (bundle_Esgk_MaximallyCircularDegreeTwoCircle_isotropicTranslationCenter ξ)) +
          MvPolynomial.C d) at hcoeff
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_map, hdistcoeff, MvPolynomial.coeff_C] at hcoeff
  have he : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single 0 2 := by
    intro h
    have hzero := DFunLike.congr_fun h 0
    simp at hzero
  simpa [he] using hcoeff

private theorem inline_Esgk_MaximallyCircularDegreeTwoCircle__isCircleFactor_of_centered_map
    {G : PlanePoly} {ξ c d : ℂ} (hc : c ≠ 0)
    (hmap : realToComplexPlanePolynomial G =
      MvPolynomial.C c * realToComplexPlanePolynomial
          (planeSquaredDistancePolynomial (bundle_Esgk_MaximallyCircularDegreeTwoCircle_isotropicTranslationCenter ξ)) +
        MvPolynomial.C d)
    {x : _root_.Point2} (hx : x ∈ PlaneCurveZeroSet G) :
    IsCircleFactor G := by
  let center : _root_.Point2 := bundle_Esgk_MaximallyCircularDegreeTwoCircle_isotropicTranslationCenter ξ
  let scalar : ℝ := G.coeff (Finsupp.single 0 2)
  have hcReal : Complex.ofReal scalar = c := by
    simpa only [scalar] using inline_Esgk_MaximallyCircularDegreeTwoCircle__centered_map_scalar_eq hmap
  have hxzero : MvPolynomial.eval (fun i : Fin 2 ↦ x i) G = 0 :=
    mem_PlaneCurveZeroSet.mp hx
  have hevalComplexification (F : PlanePoly) :
      MvPolynomial.eval (fun i : Fin 2 ↦ Complex.ofReal (x i))
          (realToComplexPlanePolynomial F) =
        Complex.ofReal (MvPolynomial.eval (fun i : Fin 2 ↦ x i) F) := by
    have hfun : (fun i : Fin 2 ↦ Complex.ofReal (x i)) =
        (Complex.ofRealHom ∘ fun i : Fin 2 ↦ x i) := by
      rfl
    rw [realToComplexPlanePolynomial, MvPolynomial.eval_map, hfun,
      ← MvPolynomial.eval_map]
    exact (MvPolynomial.map_eval Complex.ofRealHom (fun i : Fin 2 ↦ x i) F).symm
  have heval := congrArg
    (MvPolynomial.eval (fun i : Fin 2 ↦ Complex.ofReal (x i))) hmap
  have hleft :
      MvPolynomial.eval (fun i : Fin 2 ↦ Complex.ofReal (x i))
          (realToComplexPlanePolynomial G) = 0 := by
    simpa [hxzero] using hevalComplexification G
  have hdistEval :
      MvPolynomial.eval (fun i : Fin 2 ↦ Complex.ofReal (x i))
          (realToComplexPlanePolynomial (planeSquaredDistancePolynomial center)) =
        Complex.ofReal (dist x center ^ 2) := by
    rw [hevalComplexification, eval_planeSquaredDistancePolynomial]
  have heval' :
      0 = c * Complex.ofReal (dist x center ^ 2) + d := by
    simpa only [center, hleft, map_add, map_mul, MvPolynomial.eval_C,
      hdistEval] using heval
  have hd : d = -c * Complex.ofReal (dist x center ^ 2) := by
    calc
      d = (c * Complex.ofReal (dist x center ^ 2) + d) -
          c * Complex.ofReal (dist x center ^ 2) := by ring
      _ = 0 - c * Complex.ofReal (dist x center ^ 2) := by rw [← heval']
      _ = -c * Complex.ofReal (dist x center ^ 2) := by ring
  have hscalar : scalar ≠ 0 := by
    intro hzero
    apply hc
    simpa [hzero] using hcReal.symm
  have hreal :
      G = MvPolynomial.C scalar * circleEquationPolynomial center (dist x center) := by
    apply MvPolynomial.map_injective Complex.ofRealHom Complex.ofReal_injective
    change MvPolynomial.map Complex.ofRealHom G = MvPolynomial.map Complex.ofRealHom
      (MvPolynomial.C scalar * circleEquationPolynomial center (dist x center))
    rw [map_mul, MvPolynomial.map_C, circleEquationPolynomial, map_sub,
      MvPolynomial.map_C]
    have hmap' : MvPolynomial.map Complex.ofRealHom G =
        MvPolynomial.C c * MvPolynomial.map Complex.ofRealHom
            (planeSquaredDistancePolynomial center) + MvPolynomial.C d := by
      simpa only [realToComplexPlanePolynomial, center] using hmap
    have hcReal' : Complex.ofRealHom scalar = c := hcReal
    rw [hmap', hcReal', hd]
    simp only [map_neg, map_mul]
    have hofRealHom_apply (t : ℝ) : Complex.ofRealHom t = (t : ℂ) := rfl
    rw [hofRealHom_apply]
    rw [Complex.ofReal_pow]
    ring
  refine ⟨center, dist x center, dist_nonneg, ?_⟩
  rw [hreal]
  exact associated_unit_mul_left _ _
    ((isUnit_iff_ne_zero.mpr hscalar).map (MvPolynomial.C : ℝ →+* PlanePoly))

 
theorem isCircleFactor_of_maximallyCircular_degree_two_of_real_zero
    {H : PlanePoly} (hH : H ≠ 0) (hmax : IsMaximallyCircular H)
    (hdegree : H.totalDegree = 2) {x : _root_.Point2}
    (hx : x ∈ PlaneCurveZeroSet H) :
    IsCircleFactor H := by
  have hdegreeOne : H.totalDegree = 2 * 1 := by omega
  have hqdegree : (circularITangentPolynomial H).natDegree = 1 :=
    hmax.circularITangentPolynomial_natDegree hH hdegreeOne
  have hrootpos : 0 < (circularITangentPolynomial H).roots.toFinset.card := by
    apply Polynomial.roots_toFinset_card_pos_of_natDegree_pos
    rw [hqdegree]
    omega
  have hrootle : (circularITangentPolynomial H).roots.toFinset.card ≤ 1 := by
    calc
      (circularITangentPolynomial H).roots.toFinset.card ≤
          (circularITangentPolynomial H).roots.card :=
        (circularITangentPolynomial H).roots.toFinset_card_le
      _ = (circularITangentPolynomial H).natDegree :=
        IsAlgClosed.card_roots_eq_natDegree
      _ = 1 := hqdegree
  have hrootcard : (circularITangentPolynomial H).roots.toFinset.card = 1 := by omega
  obtain ⟨ξ, c, R, hc, hform, hR⟩ :=
    hmax.exists_centered_isotropic_corner_normal_form hH hdegreeOne (by omega) hrootcard
  exact inline_Esgk_MaximallyCircularDegreeTwoCircle__isCircleFactor_of_centered_map hc
    (inline_Esgk_MaximallyCircularDegreeTwoCircle__realToComplex_eq_centered_corner_one hform hR) hx

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw PachDeZeeuw.Algebraic

 
theorem finiteCarrier_selfCurveSingularAnchors_eq_univ
    {d : ℕ} (X : PreparedBipartiteInput d)
    (hself : SelfCurvePreparedInput X) (hfinite : X.C₂.Finite) :
    selfCurveSingularAnchors X = Finset.univ := by
  classical
  have hfinitePolynomial :
      (PlaneCurveZeroSet (preparedSecondCurvePolynomial X)).Finite := by
    rw [← preparedSecondCurvePolynomial_zeroSet X]
    exact hfinite
  have hsubset : PlaneCurveZeroSet (preparedSecondCurvePolynomial X) ⊆
      SingularPointSet (preparedSecondCurvePolynomial X) :=
    finite_zeroSet_subset_singularities
      (preparedSecondCurvePolynomial X) hfinitePolynomial
  apply Finset.eq_univ_of_forall
  intro p
  apply (mem_selfCurveSingularAnchors X p).2
  exact hsubset (selfCurveAnchor_mem_preparedSecondCurve_zeroSet hself p)


theorem finiteCarrier_canonicalDeletedLabels_eq_univ
    {d : ℕ} (X : PreparedBipartiteInput d)
    (hself : SelfCurvePreparedInput X) (hfinite : X.C₂.Finite) :
    selfCurveDeletedLabels X
        (selfCurveExceptionalAnchors X
          (selfCurveAxisAnchorsFromReflections X
            (selfCurveReversingCarrierSymmetries hself)))
        (selfCurveSymmetryLabels X (selfCurveCarrierSymmetries hself)) =
      Finset.univ := by
  classical
  rw [selfCurveDeletedLabels, deletedIndexedPairs, selfCurveExceptionalAnchors,
    finiteCarrier_selfCurveSingularAnchors_eq_univ X hself hfinite]
  apply Finset.eq_univ_of_forall
  intro ij
  simp [exceptionalOrderedPairs]


end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


namespace Esgk

open EuclideanGeometry
open PachDeZeeuw.Algebraic

private theorem inline_Esgk_MaximallyCircularRealCarrierNondegenerate__affineLinePolynomial_totalDegree_le_one
    (x v : PachDeZeeuw.Algebraic.Point2) :
    (affineLinePolynomial x v).totalDegree ≤ 1 := by
  have hsub0 :
      (MvPolynomial.X 0 - MvPolynomial.C (x 0) : PlanePoly).totalDegree ≤ 1 := by
    simpa using
      (MvPolynomial.totalDegree_sub_C_le
        (MvPolynomial.X 0 : PlanePoly) (x 0))
  have hsub1 :
      (MvPolynomial.X 1 - MvPolynomial.C (x 1) : PlanePoly).totalDegree ≤ 1 := by
    simpa using
      (MvPolynomial.totalDegree_sub_C_le
        (MvPolynomial.X 1 : PlanePoly) (x 1))
  have hterm0 :
      (MvPolynomial.C (v 1) *
        (MvPolynomial.X 0 - MvPolynomial.C (x 0)) : PlanePoly).totalDegree ≤ 1 := by
    calc
      _ ≤ (MvPolynomial.C (v 1) : PlanePoly).totalDegree +
          (MvPolynomial.X 0 - MvPolynomial.C (x 0) : PlanePoly).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 1 := by simpa using hsub0
  have hterm1 :
      (MvPolynomial.C (v 0) *
        (MvPolynomial.X 1 - MvPolynomial.C (x 1)) : PlanePoly).totalDegree ≤ 1 := by
    calc
      _ ≤ (MvPolynomial.C (v 0) : PlanePoly).totalDegree +
          (MvPolynomial.X 1 - MvPolynomial.C (x 1) : PlanePoly).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 1 := by simpa using hsub1
  have hsub := MvPolynomial.totalDegree_sub
      (MvPolynomial.C (v 1) * (MvPolynomial.X 0 - MvPolynomial.C (x 0)) : PlanePoly)
      (MvPolynomial.C (v 0) * (MvPolynomial.X 1 - MvPolynomial.C (x 1)))
  simpa [affineLinePolynomial] using hsub.trans (max_le hterm0 hterm1)

private theorem inline_Esgk_MaximallyCircularRealCarrierNondegenerate__affineLinePolynomial_zeroSet_infinite
    {x v : PachDeZeeuw.Algebraic.Point2} (hv : v ≠ 0) :
    (PlaneCurveZeroSet (affineLinePolynomial x v)).Infinite := by
  let f : ℝ → PachDeZeeuw.Algebraic.Point2 := fun t ↦ x + t • v
  have hf : Function.Injective f := by
    intro s t hst
    by_cases hv0 : v 0 = 0
    · have hv1 : v 1 ≠ 0 := by
        intro hv1
        apply hv
        ext i
        fin_cases i <;> assumption
      have hcoord := congrArg (fun z : PachDeZeeuw.Algebraic.Point2 ↦ z 1) hst
      change x 1 + s * v 1 = x 1 + t * v 1 at hcoord
      have hst' : (s - t) * v 1 = 0 := by linarith
      rcases mul_eq_zero.mp hst' with hst' | hv1'
      · linarith
      · exact (hv1 hv1').elim
    · have hcoord := congrArg (fun z : PachDeZeeuw.Algebraic.Point2 ↦ z 0) hst
      change x 0 + s * v 0 = x 0 + t * v 0 at hcoord
      have hst' : (s - t) * v 0 = 0 := by linarith
      rcases mul_eq_zero.mp hst' with hst' | hv0'
      · linarith
      · exact (hv0 hv0').elim
  have hmem : ∀ t : ℝ, f t ∈ PlaneCurveZeroSet (affineLinePolynomial x v) := by
    intro t
    change MvPolynomial.eval (fun i ↦ (f t) i)
      (affineLinePolynomial x v) = 0
    rw [affineLinePolynomial_eval]
    change v 1 * (x 0 + t * v 0 - x 0) -
      v 0 * (x 1 + t * v 1 - x 1) = 0
    ring
  refine (Set.infinite_range_of_injective hf).mono ?_
  rintro z ⟨t, rfl⟩
  exact hmem t

private theorem inline_Esgk_MaximallyCircularRealCarrierNondegenerate__line_set_eq_affineLinePolynomial_zeroSet
    {a b c : ℝ} (hab : (a, b) ≠ (0, 0)) :
    ∃ x v : PachDeZeeuw.Algebraic.Point2, v ≠ 0 ∧
      {p : PachDeZeeuw.Algebraic.Point2 | a * p 0 + b * p 1 = c} =
        PlaneCurveZeroSet (affineLinePolynomial x v) := by
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by
      intro hb
      exact hab (by simp [ha, hb])
    let x : PachDeZeeuw.Algebraic.Point2 := !₂[0, c / b]
    let v : PachDeZeeuw.Algebraic.Point2 := !₂[-b, 0]
    refine ⟨x, v, ?_, ?_⟩
    · intro hv
      have h0 := congrArg (fun z : PachDeZeeuw.Algebraic.Point2 ↦ z 0) hv
      have h1 := congrArg (fun z : PachDeZeeuw.Algebraic.Point2 ↦ z 1) hv
      simp [v] at h0 h1
      exact hb (by simpa using h0)
    · rw [affineLinePolynomial_zeroSet_eq_line]
      ext p
      simp [x, v, ha, hb, sub_eq_zero, eq_div_iff hb, mul_comm]
  · let x : PachDeZeeuw.Algebraic.Point2 := !₂[c / a, 0]
    let v : PachDeZeeuw.Algebraic.Point2 := !₂[-b, a]
    refine ⟨x, v, ?_, ?_⟩
    · intro hv
      have h0 := congrArg (fun z : PachDeZeeuw.Algebraic.Point2 ↦ z 0) hv
      have h1 := congrArg (fun z : PachDeZeeuw.Algebraic.Point2 ↦ z 1) hv
      simp [v] at h0 h1
      exact ha (by simpa using h1)
    · rw [affineLinePolynomial_zeroSet_eq_line]
      ext p
      simp only [Set.mem_ofPred_eq]
      simp [x, v]
      constructor <;> intro h
      · field_simp [ha] at h ⊢
        linarith
      · field_simp [ha] at h ⊢
        linarith

private theorem inline_Esgk_MaximallyCircularRealCarrierNondegenerate__irreducible_totalDegree_pos
    {G : PlanePoly} (hG : Irreducible G) : 0 < G.totalDegree := by
  apply Nat.pos_of_ne_zero
  intro hdegree
  apply hG.not_isUnit
  rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced]
  refine ⟨G.coeff 0, ?_, MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdegree⟩
  rw [isUnit_iff_ne_zero]
  intro hcoeff
  apply hG.ne_zero
  rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdegree, hcoeff, map_zero]

theorem IsMaximallyCircular.two_le_totalDegree_of_irreducible
    {G : PlanePoly} (hmax : IsMaximallyCircular G)
    (hG : Irreducible G) : 2 ≤ G.totalDegree := by
  have hpos := inline_Esgk_MaximallyCircularRealCarrierNondegenerate__irreducible_totalDegree_pos hG
  have heven := hmax.1
  omega

private theorem inline_Esgk_MaximallyCircularRealCarrierNondegenerate__totalDegree_le_of_dvd
    {G q : PlanePoly} (hG : G ∣ q) (hq : q ≠ 0) :
    G.totalDegree ≤ q.totalDegree :=
  MvPolynomial.totalDegree_le_of_dvd_of_isDomain hG hq


theorem maximallyCircular_realCarrier_not_isLineOrCircle
    {G : PlanePoly} (hGirreducible : Irreducible G)
    (hmax : IsMaximallyCircular G) (hnotCircle : ¬ IsCircleFactor G)
    {a b : PachDeZeeuw.Algebraic.Point2} (ha : a ∈ PlaneCurveZeroSet G)
    (hb : b ∈ PlaneCurveZeroSet G) (hab : a ≠ b) :
    ¬ CurveSymmetries.IsLineOrCircle (PlaneCurveZeroSet G) := by
  intro hcontrolled
  have hGdegree : 2 ≤ G.totalDegree :=
    hmax.two_le_totalDegree_of_irreducible hGirreducible
  rcases hcontrolled with hline | hcircle
  · rcases hline with ⟨α, β, γ, habcoeff, hcarrier⟩
    obtain ⟨x, v, hv, hlinezero⟩ :=
      inline_Esgk_MaximallyCircularRealCarrierNondegenerate__line_set_eq_affineLinePolynomial_zeroSet habcoeff
    have hcarrier' : PlaneCurveZeroSet G =
        PlaneCurveZeroSet (affineLinePolynomial x v) :=
      hcarrier.trans hlinezero
    have hinf :
        (PlaneCurveZeroSet G ∩
          PlaneCurveZeroSet (affineLinePolynomial x v)).Infinite := by
      rw [hcarrier']
      simpa using inline_Esgk_MaximallyCircularRealCarrierNondegenerate__affineLinePolynomial_zeroSet_infinite hv
    have hdiv : G ∣ affineLinePolynomial x v :=
      dvd_of_infinite_irreducible_zeroSet_intersection hGirreducible hinf
    have hqzero : affineLinePolynomial x v ≠ 0 :=
      (affineLinePolynomial_irreducible hv).ne_zero
    have hGle : G.totalDegree ≤
        (affineLinePolynomial x v).totalDegree :=
      inline_Esgk_MaximallyCircularRealCarrierNondegenerate__totalDegree_le_of_dvd hdiv hqzero
    have hqle : (affineLinePolynomial x v).totalDegree ≤ 1 :=
      inline_Esgk_MaximallyCircularRealCarrierNondegenerate__affineLinePolynomial_totalDegree_le_one x v
    have hGleOne : G.totalDegree ≤ 1 := hGle.trans hqle
    omega
  · rcases hcircle with ⟨center, r, hcarrier⟩
    have haSphere : a ∈ Metric.sphere center r := hcarrier ▸ ha
    have hbSphere : b ∈ Metric.sphere center r := hcarrier ▸ hb
    have hrnonneg : 0 ≤ r := by
      have hdist := Metric.mem_sphere.mp haSphere
      linarith [dist_nonneg (x := a) (y := center)]
    have hr : 0 < r := by
      rcases lt_or_eq_of_le hrnonneg with hr | rfl
      · exact hr
      · have haa : a = center := by
          apply dist_eq_zero.mp
          simpa using (Metric.mem_sphere.mp haSphere)
        have hbb : b = center := by
          apply dist_eq_zero.mp
          simpa using (Metric.mem_sphere.mp hbSphere)
        exact False.elim (hab (haa.trans hbb.symm))
    have hqzero :
        PlaneCurveZeroSet (circleEquationPolynomial center r) = Metric.sphere center r :=
      circleEquationPolynomial_zeroSet center hr.le
    have hinf :
        (PlaneCurveZeroSet G ∩
          PlaneCurveZeroSet (circleEquationPolynomial center r)).Infinite := by
      rw [hcarrier, hqzero]
      simpa using sphere_infinite center hr
    have hdiv : G ∣ circleEquationPolynomial center r :=
      dvd_of_infinite_irreducible_zeroSet_intersection hGirreducible hinf
    have hqzero' : circleEquationPolynomial center r ≠ 0 :=
      circleEquationPolynomial_ne_zero center (ne_of_gt hr)
    have hGle : G.totalDegree ≤
        (circleEquationPolynomial center r).totalDegree :=
      inline_Esgk_MaximallyCircularRealCarrierNondegenerate__totalDegree_le_of_dvd hdiv hqzero'
    have hqdegree : (circleEquationPolynomial center r).totalDegree = 2 :=
      circleEquationPolynomial_totalDegree_eq center r
    have hGdegree_le_two : G.totalDegree ≤ 2 := by
      rw [hqdegree] at hGle
      exact hGle
    have hGdegree_eq_two : G.totalDegree = 2 := by
      have heven : 2 * planeCircularLocalOrderI G = G.totalDegree := hmax.1
      omega
    exact hnotCircle
      (isCircleFactor_of_maximallyCircular_degree_two_of_real_zero
        hGirreducible.ne_zero hmax hGdegree_eq_two ha)

end Esgk

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open PachDeZeeuw (PreparedBipartiteInput)
open PachDeZeeuw.Algebraic (PlaneCurveZeroSet)
open IrreduciblePlanePolynomial


theorem selfCurveCanonicalPairSeparation
    {d : ℕ} (X : PreparedBipartiteInput d)
    (hself : SelfCurvePreparedInput X) (hd : 2 ≤ d) :
    let labels := selfCurveDeletedLabels X
      (selfCurveExceptionalAnchors X
        (selfCurveAxisAnchorsFromReflections X
          (selfCurveReversingCarrierSymmetries hself)))
      (selfCurveSymmetryLabels X (selfCurveCarrierSymmetries hself))
    labels.card ≤ 8 * d ^ 2 * X.P₁.card ∧
      ∀ ij : X.P₁ × X.P₁, ij ∉ labels →
        ∀ kl : X.P₁ × X.P₁, kl ∉ labels → ij ≠ kl →
          (twoPairDistanceCommonZeroSet (preparedSecondCurveIrreducible X)
            (ij.1 : PachDeZeeuw.Algebraic.Point2) (kl.1 : PachDeZeeuw.Algebraic.Point2)
            (ij.2 : PachDeZeeuw.Algebraic.Point2) (kl.2 : PachDeZeeuw.Algebraic.Point2)).Finite := by
  classical
  dsimp
  refine ⟨selfCurveCanonicalSymmetryFamilies_deletedLabels_card_le_eight_mul_degree_sq
    X hself hd, ?_⟩
  intro ij hij kl _hkl hne
  by_cases hfinite : X.C₂.Finite
  · rw [finiteCarrier_canonicalDeletedLabels_eq_univ X hself hfinite] at hij
    exact False.elim (hij (Finset.mem_univ ij))
  let C := preparedSecondCurveIrreducible X
  have hnot : ¬ CurveSymmetries.IsLineOrCircle (PlaneCurveZeroSet C.polynomial) := by
    change ¬ CurveSymmetries.IsLineOrCircle
      (PlaneCurveZeroSet (preparedSecondCurvePolynomial X))
    rw [← preparedSecondCurvePolynomial_zeroSet X]
    exact selfCurvePreparedInput_not_isLineOrCircle hself
  have hlabels : ((ij.1 : PachDeZeeuw.Algebraic.Point2), (ij.2 : PachDeZeeuw.Algebraic.Point2)) ≠
      ((kl.1 : PachDeZeeuw.Algebraic.Point2), (kl.2 : PachDeZeeuw.Algebraic.Point2)) := by
    intro heq
    apply hne
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst heq
    · apply Subtype.ext
      exact congrArg Prod.snd heq
  by_cases hrepeated : (ij.1 : PachDeZeeuw.Algebraic.Point2) = (kl.1 : PachDeZeeuw.Algebraic.Point2) ∨
      (ij.2 : PachDeZeeuw.Algebraic.Point2) = (kl.2 : PachDeZeeuw.Algebraic.Point2)
  · exact twoPairDistanceCommonZeroSet_finite_of_repeated_anchor
      C hnot _ _ _ _ hlabels hrepeated
  have hac : (ij.1 : PachDeZeeuw.Algebraic.Point2) ≠ (kl.1 : PachDeZeeuw.Algebraic.Point2) :=
    fun h ↦ hrepeated (Or.inl h)
  have hbe : (ij.2 : PachDeZeeuw.Algebraic.Point2) ≠ (kl.2 : PachDeZeeuw.Algebraic.Point2) :=
    fun h ↦ hrepeated (Or.inr h)
  obtain ⟨g₁, r₁, hr₁, hg₁a, hg₁c, _⟩ :=
    C.exists_affineIsometryTransport_normalizedDistancePair hac
  obtain ⟨g₂, r₂, hr₂, hg₂b, hg₂e, _⟩ :=
    C.exists_affineIsometryTransport_normalizedDistancePair hbe
  have hanchors := endpoints_not_mem_canonicalAxis_and_nonsingular_of_not_mem_deletedLabel
    X _ _ hij
  have hns₁ := normalized_nonreflection_of_not_mem_canonicalAxis
    X hself ij.1 hanchors.1.1 g₁ (-r₁) hg₁a
  have hns₂ := normalized_nonreflection_of_not_mem_canonicalAxis
    X hself ij.2 hanchors.2.1 g₂ (-r₂) hg₂b
  by_contra hinfinite
  obtain ⟨T, hTcarrier, hTa, _hTc⟩ :=
    exists_affineIsometry_carrier_symmetry_of_infinite_intersection_of_nonsingular
      C g₁ g₂ hr₁.ne' hr₂.ne' hns₁ hns₂
      (ij.1 : PachDeZeeuw.Algebraic.Point2) (kl.1 : PachDeZeeuw.Algebraic.Point2) (ij.2 : PachDeZeeuw.Algebraic.Point2) (kl.2 : PachDeZeeuw.Algebraic.Point2)
      hg₁a hg₁c hg₂b hg₂e hinfinite
      (selfCurveAnchor_mem_preparedSecondCurve_zeroSet hself ij.1)
      hanchors.1.2
  have hTX : T.toIsometryEquiv '' X.C₂ = X.C₂ := by
    rw [preparedSecondCurvePolynomial_zeroSet X]
    exact hTcarrier
  have hTmem : T.toIsometryEquiv ∈ selfCurveCarrierSymmetries hself :=
    (mem_selfCurveCarrierSymmetries hself _).2 hTX
  have hsym := (anchors_not_mem_of_label_not_mem_selfCurveDeletedLabels hij).2.2
  exact hsym ((mem_selfCurveSymmetryLabels X _ ij).2
    ⟨T.toIsometryEquiv, hTmem, hTa⟩)

end Esgk

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


namespace Esgk

open PachDeZeeuw (PreparedBipartiteInput)
open PachDeZeeuw.Algebraic (PlanePoly PlaneCurveZeroSet)
open IrreduciblePlanePolynomial

theorem maximallyCircular_pairSeparation
    {G : PlanePoly} (hGirreducible : Irreducible G)
    (hmax : IsMaximallyCircular G) (hnotCircle : ¬ IsCircleFactor G)
    (S : Finset PachDeZeeuw.Algebraic.Point2) (hS : (S : Set PachDeZeeuw.Algebraic.Point2) ⊆ PlaneCurveZeroSet G) :
    ∃ Δ : Finset (S × S),
      Δ.card ≤ 8 * G.totalDegree ^ 2 * S.card ∧
      ∀ ij, ij ∉ Δ → ∀ kl, kl ∉ Δ → ij ≠ kl →
        (twoPairDistanceCommonZeroSet
          ⟨G, hGirreducible⟩
          (ij.1 : PachDeZeeuw.Algebraic.Point2) (kl.1 : PachDeZeeuw.Algebraic.Point2)
          (ij.2 : PachDeZeeuw.Algebraic.Point2) (kl.2 : PachDeZeeuw.Algebraic.Point2)).Finite := by
  classical
  by_cases hsmall : S.card < 2
  · refine ⟨Finset.univ, ?_, ?_⟩
    · have hcases : S.card = 0 ∨ S.card = 1 := by omega
      rcases hcases with hzero | hone
      · simp [hzero]
      · have hdegree : 2 ≤ G.totalDegree :=
          hmax.two_le_totalDegree_of_irreducible hGirreducible
        simp [hone]
        nlinarith
    · intro ij hij
      exact False.elim (hij (Finset.mem_univ ij))
  · have hlarge : 1 < S.card := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hlarge
    have hnot : ¬ CurveSymmetries.IsLineOrCircle
        (PlaneCurveZeroSet G) :=
      maximallyCircular_realCarrier_not_isLineOrCircle hGirreducible hmax
        hnotCircle (hS ha) (hS hb) hab
    have hnotPlane : ¬ PlaneCurve.IsLineOrCircle
        (PlaneCurveZeroSet G) := by
      intro hcontrolled
      apply hnot
      simpa [PlaneCurve.IsLineOrCircle,
        CurveSymmetries.IsLineOrCircle] using hcontrolled
    let C : Set PachDeZeeuw.Algebraic.Point2 := PlaneCurveZeroSet G
    have hnotExceptional : ¬ PachDeZeeuw.ExceptionalCurvePair C C := by
      intro hExc
      apply hnot
      simpa [C, PlaneCurve.IsLineOrCircle,
        CurveSymmetries.IsLineOrCircle] using
        PachDeZeeuw.ExceptionalCurvePair.left_controlledDegenerate hExc
    let X : PreparedBipartiteInput G.totalDegree :=
      { C₁ := C
        C₂ := C
        P₁ := S
        P₂ := ∅
        hC₁ := ⟨G, hGirreducible.ne_zero, le_rfl, hGirreducible, rfl⟩
        hC₂ := ⟨G, hGirreducible.ne_zero, le_rfl, hGirreducible, rfl⟩
        hP₁ := by simpa [C] using hS
        hP₂ := by simp
        notExceptional := hnotExceptional
        assumption31 := by
          apply PachDeZeeuw.assumption31Data_of_not_controlledDegenerate
            hnotPlane hnotPlane
          · simp
          · exact hnotExceptional }
    have hsep := selfCurveCanonicalPairSeparation X (by rfl)
      (hmax.two_le_totalDegree_of_irreducible hGirreducible)
    dsimp at hsep
    let Δ : Finset (S × S) :=
      selfCurveDeletedLabels X
        (selfCurveExceptionalAnchors X
          (selfCurveAxisAnchorsFromReflections X
            (selfCurveReversingCarrierSymmetries (X := X) (by rfl))))
        (selfCurveSymmetryLabels X (selfCurveCarrierSymmetries (X := X) (by rfl)))
    have hcard : Δ.card ≤ 8 * G.totalDegree ^ 2 * S.card := by
      simpa [Δ, X] using hsep.1
    have hzero :
        PlaneCurveZeroSet (preparedSecondCurveIrreducible X).polynomial =
          PlaneCurveZeroSet G := by
      change PlaneCurveZeroSet (preparedSecondCurvePolynomial X) =
        PlaneCurveZeroSet G
      simpa [X, C] using (preparedSecondCurvePolynomial_zeroSet X).symm
    refine ⟨Δ, hcard, ?_⟩
    intro ij hij kl hkl hne
    have hfin := hsep.2 ij hij kl hkl hne
    simpa only [twoPairDistanceCommonZeroSet, hzero] using hfin

end Esgk

end


/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


open Esgk
section

open PachDeZeeuw.Algebraic (PlanePoly PlaneCurveZeroSet)
open IrreduciblePlanePolynomial


theorem solution
    {G : PlanePoly} (hGirreducible : Irreducible G)
    (hmax : IsMaximallyCircular G) (hnotCircle : ¬ IsCircleFactor G)
    (S₁ S₂ : Finset PachDeZeeuw.Algebraic.Point2)
    (hS₁ : (S₁ : Set PachDeZeeuw.Algebraic.Point2) ⊆ PlaneCurveZeroSet G)
    (hS₂ : (S₂ : Set PachDeZeeuw.Algebraic.Point2) ⊆ PlaneCurveZeroSet G) :
    ∃ (Δ₁ : Finset (S₁ × S₁)) (Δ₂ : Finset (S₂ × S₂)),
      Δ₁.card ≤ 8 * G.totalDegree ^ 2 * S₁.card ∧
      Δ₂.card ≤ 8 * G.totalDegree ^ 2 * S₂.card ∧
      (∀ ij, ij ∉ Δ₁ → ∀ kl, kl ∉ Δ₁ → ij ≠ kl →
        (twoPairDistanceCommonZeroSet
          ⟨G, hGirreducible⟩
          (ij.1 : PachDeZeeuw.Algebraic.Point2) (kl.1 : PachDeZeeuw.Algebraic.Point2)
          (ij.2 : PachDeZeeuw.Algebraic.Point2) (kl.2 : PachDeZeeuw.Algebraic.Point2)).Finite) ∧
      (∀ ij, ij ∉ Δ₂ → ∀ kl, kl ∉ Δ₂ → ij ≠ kl →
        (twoPairDistanceCommonZeroSet
          ⟨G, hGirreducible⟩
          (ij.1 : PachDeZeeuw.Algebraic.Point2) (kl.1 : PachDeZeeuw.Algebraic.Point2)
          (ij.2 : PachDeZeeuw.Algebraic.Point2) (kl.2 : PachDeZeeuw.Algebraic.Point2)).Finite) := by
  obtain ⟨Δ₁, hcard₁, hfinite₁⟩ :=
    maximallyCircular_pairSeparation hGirreducible hmax hnotCircle S₁ hS₁
  obtain ⟨Δ₂, hcard₂, hfinite₂⟩ :=
    maximallyCircular_pairSeparation hGirreducible hmax hnotCircle S₂ hS₂
  exact ⟨Δ₁, Δ₂, hcard₁, hcard₂, hfinite₁, hfinite₂⟩

end
