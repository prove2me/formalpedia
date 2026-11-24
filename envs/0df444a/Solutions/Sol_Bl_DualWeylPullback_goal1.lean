-- Prove2me | solution 1 for Bl.DualWeylPullback.goal1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:36:40.07958+00:00
-- url     : https://prove2.me/submissions/710e6722-c133-4594-8258-1e5546ab1ac0

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_LatRetract
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_TensorKP
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_LemmaSMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_WeylDimPosOfAntitone
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_HarProjEqZeroIff
import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_DigitClassCount
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjSeg
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjBridge
import Definitions.Def_Formalism_LocalRingCardinality_Params
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_LocalRingCardinality_DataCoeff
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_LocalRingCardinality_DataKernels
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_DataS
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjPol
import Definitions.Def_Formalism_MahlerMeasure_WithMargin
import Definitions.Def_Formalism_SubspaceCounting_ChoiceOfTopsRefined
import Definitions.Def_Formalism_GrowthSums_LemmaATwoFactList
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitsPlaces
import Definitions.Def_Formalism_FrobeniusOrbits_HostDiffSupport
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitCountSg
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_CoboundaryTransfers_Statement
import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_FrameTransport
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataGChain
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_SegRing
import Definitions.Def_Formalism_PolynomialDimension_DetMulEqSumAdjugate
import Definitions.Def_Formalism_PolynomialDimension_FinalNum
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_Imports
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_OrbitSum
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_ChainScalar
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_LatLiftIndep
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_GaussOp
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_EigenSwap
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_FFPlancherel
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_DetSwap
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_DiscriminantRealSubfield
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickFrames
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FinSup
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RatioMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNStep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PiSumForallInsertOnly
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Example
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_GramBlock
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RescaleCovol
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_TwistFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtImage
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_QuotRealize
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FrameLinearAlgebraFirst
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Actions
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AutomorphicFormsDecompositionHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeAssoc
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeConvolutionMemHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LocalAlgebraInertPrime
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckebasic
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_InclusionInjective
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Ipindep
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelvsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LinSubstIsHomogeneous
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Nabladual
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureConjugationInvariant
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureExists
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SplitUnitaryGroupIso
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabfin
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stdform
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Transport
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Upqcpt
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_DualWeylModuleStable
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Definitions.Def_Formalism_SatakeDualWeyl_DualWeylRepApply
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_Point
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_HarderNarasimhan_StatementFrame
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_CorankShare_CorankShareProofs_LayerCakeFormula
import Definitions.Def_Formalism_CorankShare_CorankShareProofs_SumNormSqLeHilbertSchmidt
import Definitions.Def_Formalism_HarderNarasimhan_StatementFrameF
import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckecomm
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SphericalA
import Definitions.Def_Formalism_TameInertiaTowers_FinalGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_Galois
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_ConjEqInvOfPowEqOne
import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ThetaBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ExampleZ
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_NeighbourBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_FinIntermediate
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomOfTrace
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualOrthSum
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusScale
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetAssembly
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_OpBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovol
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_QuadDiscr
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_APLogDensity
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_HostDensityArith
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_MQGalois
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_MQKummer
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_MQFrob
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_KroneckerMeaning
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_TypesA
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_TypesB
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostFrob
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostConj
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostInertia
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostMu
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostEmb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_HermitianLattices_DefsCS
import Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Formalism_HermitianLattices_DiscrFinite
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_StatementB
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantCompactSpan
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantOrthogonalInf
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_MinkCore
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_GjLevel
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_GjScale
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_SuccMin
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_AdaptedBasis
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_MeasureEqCovolumeMulVolumeImage
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NewtonSlope
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_MinkowskiIILowerOf
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NPWDivision
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NPUnit
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementD
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuadraticInequalityBoundHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SumOfSquaresIdentityHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CasKHW
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HWDiag
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_TrPowSumFilterZero
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnG
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementA
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementC
import Definitions.Def_Lemmata_DualWeylPullback_DualWeylPull
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylRowStable
import Theorems.Thm_Formalism_GradedWeylDivisibility_nablaLTwMem
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowActMul
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_Formalism_ThetaLiftIndependence_ChainScalarLemmas_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
namespace Bl.DualWeylPullback
private lemma map_aeval_nat {O K σ τ : Type} [CommRing O] [CommRing K] (φ : O →+* K)
    (h : σ → MvPolynomial τ O) (f : MvPolynomial σ O) :
    MvPolynomial.map φ (MvPolynomial.aeval h f) =
      MvPolynomial.aeval (fun v => MvPolynomial.map φ (h v)) (MvPolynomial.map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.aeval_C, MvPolynomial.map_C, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp => simp only [map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X, hp]
private lemma rowAct_map {O K : Type} [CommRing O] [CommRing K] (φ : O →+* K) {k n : ℕ}
    (A : Matrix (Fin k) (Fin k) O) (f : MvPolynomial (Fin k × Fin n) O) :
    MvPolynomial.map φ (Formalism.GradedWeylDivisibility.rowAct O A f) = Formalism.GradedWeylDivisibility.rowAct K (A.map φ) (MvPolynomial.map φ f) := by
  unfold Formalism.GradedWeylDivisibility.rowAct
  rw [map_aeval_nat]
  congr 1
  congr 1
  funext v
  simp [map_sum]
private lemma colAddGen_map {O K : Type} [CommRing O] [CommRing K] (φ : O →+* K) {k n : ℕ}
    (l j : Fin n) (f : MvPolynomial (Fin k × Fin n) O) :
    MvPolynomial.map φ (Formalism.GradedWeylDivisibility.colAddGen O l j f) = Formalism.GradedWeylDivisibility.colAddGen K l j (MvPolynomial.map φ f) := by
  unfold Formalism.GradedWeylDivisibility.colAddGen
  rw [map_aeval_nat]
  congr 1
  congr 1
  funext v
  split_ifs <;> simp
private lemma dualWeyl_pull {O K : Type} [CommRing O] [CommRing K] (φ : O →+* K)
    (hφ : Function.Injective φ) {r n : ℕ} (ν : Fin n → ℕ) (f : MvPolynomial (Fin r × Fin n) O)
    (hf : MvPolynomial.map φ f ∈ Formalism.GradedWeylDivisibility.dualWeyl K r n ν) : f ∈ Formalism.GradedWeylDivisibility.dualWeyl O r n ν := by
  unfold Formalism.GradedWeylDivisibility.dualWeyl at hf ⊢
  simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, MvPolynomial.mem_weightedHomogeneousSubmodule] at hf ⊢
  refine ⟨?_, ?_⟩
  · intro d hd
    exact hf.1 (by
      rw [MvPolynomial.coeff_map]
      intro h0
      exact hd (hφ (by rw [h0, map_zero])))
  · intro l j hlj
    apply MvPolynomial.map_injective φ hφ
    rw [colAddGen_map, MvPolynomial.map_rename]
    exact hf.2 l j hlj
private lemma span_mat {O K : Type} [CommRing O] [Field K] [Algebra O K] {k : ℕ}
    (g g' : Matrix (Fin k) (Fin k) K) (h : Formalism.MainNotions.G.colSpan O g' ≤ Formalism.MainNotions.G.colSpan O g) :
    ∃ A : Matrix (Fin k) (Fin k) O, g' = g * A.map (algebraMap O K) := by
  have hc : ∀ c : Fin k, ∃ a : Fin k → O, ∑ i, a i • (fun r => g r i) = fun r => g' r c := by
    intro c
    have h1 : (fun r => g' r c) ∈ Formalism.MainNotions.G.colSpan O g' := Submodule.subset_span ⟨c, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun O).1 (h h1)
  choose a ha using hc
  refine ⟨Matrix.of fun i c => a c i, ?_⟩
  ext r c
  have h2 := congrFun (ha c) r
  simp only [Finset.sum_apply, Pi.smul_apply] at h2
  rw [← h2, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [Algebra.smul_def, mul_comm]
private lemma span_unit {O K : Type} [CommRing O] [Field K] [Algebra O K]
    (hφ : Function.Injective (algebraMap O K)) {k : ℕ} (g g' : Matrix (Fin k) (Fin k) K)
    (hg : IsUnit g.det) (h : Formalism.MainNotions.G.colSpan O g = Formalism.MainNotions.G.colSpan O g') :
    ∃ A : Matrix (Fin k) (Fin k) O, IsUnit A.det ∧ g' = g * A.map (algebraMap O K) := by
  obtain ⟨A, hA⟩ := span_mat g g' h.ge
  obtain ⟨B, hB⟩ := span_mat g' g h.le
  refine ⟨A, ?_, hA⟩
  have h1 : g * (A * B).map (algebraMap O K) = g * 1 := by
    rw [Matrix.map_mul, ← Matrix.mul_assoc, ← hA, ← hB, Matrix.mul_one]
  have h2 : (A * B).map (algebraMap O K) = 1 := by
    have h3 := congrArg (fun M => g⁻¹ * M) h1
    simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul g hg] using h3
  have h3 : A * B = 1 := by
    apply Matrix.map_injective hφ
    simpa using h2
  have h4 : A.det * B.det = 1 := by rw [← Matrix.det_mul, h3, Matrix.det_one]
  exact ⟨⟨A.det, B.det, h4, by rw [mul_comm]; exact h4⟩, rfl⟩
private lemma clear_den {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] (w : O) (hw : Irreducible w) {σ : Type} (G : MvPolynomial σ K) :
    ∃ n : ℕ, ∃ G0 : MvPolynomial σ O,
      MvPolynomial.map (algebraMap O K) G0 = algebraMap O K (w ^ n) • G := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O) G.coeffs
  have hb0 : (b : O) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hw
  refine ⟨n, ?_⟩
  have hr : algebraMap O K (w ^ n) • G ∈ Set.range (MvPolynomial.map (algebraMap O K)) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro x hx
    rw [Finset.mem_coe, MvPolynomial.mem_coeffs_iff] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    rw [MvPolynomial.coeff_smul, smul_eq_mul]
    have hd' : G.coeff d ≠ 0 := by
      intro h0
      apply MvPolynomial.mem_support_iff.1 hd
      rw [MvPolynomial.coeff_smul, h0, smul_zero]
    obtain ⟨y, hy⟩ := hb _ (MvPolynomial.coeff_mem_coeffs _ hd')
    have hu1 : algebraMap O K (↑u⁻¹ : O) * algebraMap O K (↑u : O) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    refine ⟨(↑u⁻¹ : O) * y, ?_⟩
    rw [map_mul, hy, Algebra.smul_def, hu, map_mul]
    linear_combination (algebraMap O K (w ^ n) * G.coeff d) * hu1
  obtain ⟨G0, h0⟩ := hr
  exact ⟨G0, h0⟩
end Bl.DualWeylPullback
end

set_option autoImplicit false
open Bl Bl.DualWeylPullback
namespace Bl.DualWeylPullback
theorem _root_.solution :
  ∀ {O K : Type} [inst : CommRing.{0} O] [inst_1 : IsDomain.{0} O] [IsDiscreteValuationRing.{0} O] [inst_3 : Field.{0} K]
  [inst_4 : Algebra.{0, 0} O K] [IsFractionRing.{0, 0} O K] (w : O),
  Irreducible.{0} w →
    ∀ (m : Nat) (mu : Fin (HAdd.hAdd.{0, 0, 0} m 1) → Int),
      Antitone.{0, 0} mu →
        ∀ (g : Matrix.{0, 0, 0} (Fin (HAdd.hAdd.{0, 0, 0} m 1)) (Fin (HAdd.hAdd.{0, 0, 0} m 1)) K),
          IsUnit.{0} (Matrix.det.{0, 0} g) →
            ∀ (F : MvPolynomial.{0, 0} (Prod.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} m 1)) (Fin (HAdd.hAdd.{0, 0, 0} m 1))) K),
              Membership.mem.{0, 0}
                  (Formalism.GradedWeylDivisibility.dualWeyl.{0} K (HAdd.hAdd.{0, 0, 0} m 1) (HAdd.hAdd.{0, 0, 0} m 1) (Formalism.MainNotions.G.nuOf mu)) F →
                Exists.{1} fun (n : Nat) ↦
                  Membership.mem.{0, 0} (Formalism.MainNotions.G.H0.{0, 0} O m mu (Formalism.MainNotions.G.colSpan.{0, 0} O g))
                    (HSMul.hSMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} w n) F) := by
  intro O K _ _ _ _ _ _ w hw m mu hmu g hg F hF
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hG : g.det ^ mu (Fin.last m) • Formalism.GradedWeylDivisibility.rowAct K g F ∈
      Formalism.GradedWeylDivisibility.dualWeyl K (m + 1) (m + 1) (Formalism.MainNotions.G.nuOf mu) :=
    Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable K _ _ _ g F hF)
  obtain ⟨n, G0, hG0⟩ := clear_den w hw (g.det ^ mu (Fin.last m) • Formalism.GradedWeylDivisibility.rowAct K g F)
  have hG0m : G0 ∈ Formalism.GradedWeylDivisibility.dualWeyl O (m + 1) (m + 1) (Formalism.MainNotions.G.nuOf mu) :=
    dualWeyl_pull _ hinj _ G0 (by rw [hG0]; exact Submodule.smul_mem _ _ hG)
  refine ⟨n, ?_⟩
  unfold Formalism.MainNotions.G.H0
  rw [if_pos hmu]
  simp only [Submodule.mem_iInf]
  rintro g' ⟨hg', hspan⟩
  obtain ⟨A, hA, rfl⟩ := span_unit hinj g g' hg hspan
  rw [Formalism.GradedWeylDivisibility.nablaLTwMem O K m mu _ hg']
  obtain ⟨U, hU⟩ := hA
  refine ⟨(↑(U ^ mu (Fin.last m)) : O) • Formalism.GradedWeylDivisibility.rowAct O A G0,
    Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable O _ _ _ A G0 hG0m), ?_⟩
  change MvPolynomial.map (algebraMap O K) ((↑(U ^ mu (Fin.last m)) : O) • Formalism.GradedWeylDivisibility.rowAct O A G0) = _
  have hz : algebraMap O K ↑(U ^ mu (Fin.last m)) = (algebraMap O K ↑U) ^ mu (Fin.last m) := by
    have h5 : ((Units.map (algebraMap O K).toMonoidHom (U ^ mu (Fin.last m)) : Kˣ) : K) =
        algebraMap O K ↑(U ^ mu (Fin.last m)) := rfl
    rw [← h5, map_zpow, Units.val_zpow_eq_zpow_val]
    rfl
  have hdet : (A.map (algebraMap O K)).det = algebraMap O K A.det := by
    rw [RingHom.map_det]
    rfl
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul,
    rowAct_map, hG0, Matrix.det_mul, hdet, ← hU, hz,
    ← Formalism.GradedWeylDivisibility.rowActMul K (m + 1) (m + 1) (A.map (algebraMap O K)) g, AlgHom.comp_apply,
    ← algebraMap_smul K (w ^ n) F]
  simp only [map_smul, smul_smul]
  congr 1
  rw [mul_zpow]
  ring
end Bl.DualWeylPullback
