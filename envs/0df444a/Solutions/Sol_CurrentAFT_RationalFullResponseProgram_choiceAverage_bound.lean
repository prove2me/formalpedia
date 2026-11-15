-- Prove2me | solution 1 for CurrentAFT.RationalFullResponseProgram.choiceAverage_bound
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T21:18:15.000444+00:00
-- url     : https://prove2.me/submissions/4faff718-6829-4661-839c-6f6b4d79afec

import Definitions.Def_InfoLossLAR_NativeBundle_12
import Mathlib
namespace AFT
end AFT
namespace AFT.finiteCorrection
end AFT.finiteCorrection
namespace P2M60f02c0e
end P2M60f02c0e
section
namespace AFT
open scoped BigOperators
section RankOne
variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
end RankOne
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h3 (ρ scalar : ℝ) (hsmall : |scalar| ≤ ρ / 2) :
    ρ / 2 ≤ ρ + scalar := by
  have := (abs_le.mp hsmall).1
  linarith
open _root_.P2M60f02c0e renaming h3 → _p2mH3
section ContinuousLocalInverse
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [CompleteSpace E]
end ContinuousLocalInverse
section BoundaryCollapse
variable {ι : Type*} [DecidableEq ι]
end BoundaryCollapse
section ConjugatedProjection
variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
end ConjugatedProjection
end AFT
open _root_.P2M60f02c0e renaming h3 → _p2mH3
end
open _root_.P2M60f02c0e renaming h3 → _p2mH3
namespace AFT.basePrimaryProfile
end AFT.basePrimaryProfile
namespace AFT.calibratedBodyProfile
end AFT.calibratedBodyProfile
namespace AFT.calibratedPrimaryProfile
end AFT.calibratedPrimaryProfile
namespace AFT.calibratedReferenceMean
end AFT.calibratedReferenceMean
namespace AFT.diffuseEndpointMean
end AFT.diffuseEndpointMean
section
namespace AFT
open scoped BigOperators
section FiniteProfiles
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
end FiniteProfiles
section SignProfile
variable {ι : Type*} [Fintype ι]
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h2 (activation : ℝ) (signProfile sign : ι → ℝ)
    (hsign : ∀ color, |sign color| ≤ 1)
    (hsmall : (∑ color, |signProfile color|) < activation) (profile : ι → ℝ) :
    (_root_.AFT.finitePrimaryRankEquiv activation signProfile sign hsign hsmall).symm profile =
      profile - ((activation + _root_.AFT.signFunctional sign signProfile)⁻¹ *
        _root_.AFT.signFunctional sign profile) • signProfile := by
  exact _root_.AFT.primaryRankInverse_apply activation signProfile (_root_.AFT.profileSignMap sign) profile
open _root_.P2M60f02c0e renaming h2 → _p2mH2
end SignProfile
open _root_.P2M60f02c0e renaming h2 → _p2mH2
end AFT
open _root_.P2M60f02c0e renaming h2 → _p2mH2
end
open _root_.P2M60f02c0e renaming h2 → _p2mH2
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.actualBodyShiftProgram
end AFT.V7Calibration.actualBodyShiftProgram
namespace AFT.V7Calibration.actualLegWindowEquiv
end AFT.V7Calibration.actualLegWindowEquiv
namespace AFT.V7Calibration.actualPairSourceApproxLaw
end AFT.V7Calibration.actualPairSourceApproxLaw
namespace AFT.V7Calibration.actualPairSourceProgram
end AFT.V7Calibration.actualPairSourceProgram
namespace AFT.V7Calibration.rational_expectation_error
end AFT.V7Calibration.rational_expectation_error
section
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators
noncomputable section
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
attribute [local instance] _root_.AFT.V7Calibration.sliceProgramFinDecEq
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h1 (modulus boundary shift color : ℤ) :
    |(_root_.AFT.V7Calibration.sliceProbabilityProgram modulus boundary shift color : ℝ)|≤1 := by
  rw [_root_.AFT.V7Calibration.sliceProbabilityProgram_eq_original]
  split_ifs with hh
  · simp only [Rat.cast_inv,Rat.cast_natCast]
    rw [abs_of_nonneg (by positivity)]
    apply inv_le_one_of_one_le₀
    exact_mod_cast (Finset.one_le_card.mpr ⟨color,hh⟩)
  · norm_num
open _root_.P2M60f02c0e renaming h1 → _p2mH1
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h0 (modulus boundary start source : ℤ) (width : ℕ) (color : ℤ) :
    |(_root_.AFT.V7Calibration.averagedSliceProgram modulus boundary start source width color : ℝ)|≤1 := by
  by_cases hw : width=0
  · subst width
    simp [_root_.AFT.V7Calibration.averagedSliceProgram_eq_sum,_root_.AFT.anchorInterval]
  simp only [_root_.AFT.V7Calibration.averagedSliceProgram_eq_sum,Rat.cast_sum,Rat.cast_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ shift∈_root_.AFT.anchorInterval start width,_root_.AFT.intervalAnchorLaw start width shift := by
      apply Finset.sum_le_sum
      intro shift _
      rw [abs_mul,_root_.AFT.V7Calibration.intervalProbabilityProgram_cast,abs_of_nonneg (_root_.AFT.intervalAnchorLaw_nonneg _ _ _)]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (_p2mH1 modulus boundary (shift-source) color)
        (_root_.AFT.intervalAnchorLaw_nonneg start shift width)
    _ = 1 := _root_.AFT.intervalAnchorLaw_mass start width hw
open _root_.P2M60f02c0e renaming h0 → _p2mH0
end
open _root_.P2M60f02c0e renaming h0 → _p2mH0
open _root_.P2M60f02c0e renaming h1 → _p2mH1
end AFT.V7Calibration
open _root_.P2M60f02c0e renaming h0 → _p2mH0
open _root_.P2M60f02c0e renaming h1 → _p2mH1
end
open _root_.P2M60f02c0e renaming h0 → _p2mH0
open _root_.P2M60f02c0e renaming h1 → _p2mH1
namespace AFT.averagedIntervalTranslationOperator
end AFT.averagedIntervalTranslationOperator
namespace AFT.primaryActivity
end AFT.primaryActivity
namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.DiffuseProfiles
end CurrentAFT.DiffuseProfiles
namespace CurrentAFT.DiffuseProfiles.actual_clearance
end CurrentAFT.DiffuseProfiles.actual_clearance
namespace CurrentAFT.DiffuseProfiles.deletion
end CurrentAFT.DiffuseProfiles.deletion
namespace CurrentAFT.DiffuseProfiles.intervalStart
end CurrentAFT.DiffuseProfiles.intervalStart
namespace CurrentAFT.DiffuseProfiles.signProfile
end CurrentAFT.DiffuseProfiles.signProfile
namespace CurrentAFT.Parameters
end CurrentAFT.Parameters
namespace CurrentAFT.Parameters.anchorWidth
end CurrentAFT.Parameters.anchorWidth
namespace CurrentAFT.Parameters.sourceWidth
end CurrentAFT.Parameters.sourceWidth
section
namespace CurrentAFT.FirstResponse
open AFT DiffuseProfiles
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth
  Parameters.sourceCutoff DiffuseProfiles.actualProfile DiffuseProfiles.signProfile
  DiffuseProfiles.activation DiffuseProfiles.actualSeedLaw
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h37 (security : ℕ) :
    _root_.CurrentAFT.DiffuseProfiles.activation security / 2 ≤ _root_.CurrentAFT.DiffuseProfiles.activation security +
      _root_.AFT.signFunctional (_root_.CurrentAFT.FirstResponse.anchorSign security) (_root_.CurrentAFT.DiffuseProfiles.signProfile security) :=
  _p2mH3 _ _
    ((_root_.AFT.signFunctional_abs_le_l1 (_root_.CurrentAFT.FirstResponse.anchorSign security) (_root_.CurrentAFT.DiffuseProfiles.signProfile security)
      (_root_.CurrentAFT.FirstResponse.anchorSign_abs_le_one security)).trans (_root_.CurrentAFT.FirstResponse.signProfile_l1_le_half_activation security))
open _root_.P2M60f02c0e renaming h37 → _p2mH37
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h38 (security : ℕ) (profile : _root_.CurrentAFT.FirstResponse.Palette security → ℝ) :
    (_root_.CurrentAFT.FirstResponse.responseEquiv security).symm profile = profile -
      ((_root_.CurrentAFT.DiffuseProfiles.activation security + _root_.AFT.signFunctional (_root_.CurrentAFT.FirstResponse.anchorSign security) (_root_.CurrentAFT.DiffuseProfiles.signProfile security))⁻¹ *
        _root_.AFT.signFunctional (_root_.CurrentAFT.FirstResponse.anchorSign security) profile) • _root_.CurrentAFT.DiffuseProfiles.signProfile security :=
  _p2mH2 _ _ _ _ _ _
open _root_.P2M60f02c0e renaming h38 → _p2mH38
end
open _root_.P2M60f02c0e renaming h37 → _p2mH37
open _root_.P2M60f02c0e renaming h38 → _p2mH38
end CurrentAFT.FirstResponse
open _root_.P2M60f02c0e renaming h37 → _p2mH37
open _root_.P2M60f02c0e renaming h38 → _p2mH38
end
open _root_.P2M60f02c0e renaming h37 → _p2mH37
open _root_.P2M60f02c0e renaming h38 → _p2mH38
namespace CurrentAFT.ControlCoordinates
end CurrentAFT.ControlCoordinates
namespace CurrentAFT.ControlCoordinates.centerBodySlot
end CurrentAFT.ControlCoordinates.centerBodySlot
namespace CurrentAFT.ControlCoordinates.centerPrimarySlot
end CurrentAFT.ControlCoordinates.centerPrimarySlot
namespace CurrentAFT.ControlCoordinates.coefficientStatistic
end CurrentAFT.ControlCoordinates.coefficientStatistic
namespace CurrentAFT.ControlCoordinates.kernelMean
end CurrentAFT.ControlCoordinates.kernelMean
namespace CurrentAFT.ControlCoordinates.pairedLift
end CurrentAFT.ControlCoordinates.pairedLift
namespace CurrentAFT.ControlCoordinates.twoPoolUStatistic
end CurrentAFT.ControlCoordinates.twoPoolUStatistic
section
namespace CurrentAFT.ControlProduct
open AFT ControlCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.ControlProduct.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.ControlProduct.classicalSumDecidableEq
variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]
section SlotSpaces
variable {PS BS PT BT : Type*} [Fintype PS] [Fintype BS] [Fintype PT] [Fintype BT]
variable {PU BU : Type*} [Fintype PU] [Fintype BU]
end SlotSpaces
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h25 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    {r s r' s' : ℕ} (first : _root_.CurrentAFT.ControlCoordinates.canonicalKernels primary body r s)
    (second : _root_.CurrentAFT.ControlCoordinates.canonicalKernels primary body r' s')
    (colors : Fin (r + r') → Primary) (centers : Fin (s + s') → Body) :
    (_root_.CurrentAFT.ControlProduct.homogeneousProduct primary body first second).val colors centers =
      ((r + r').factorial : ℝ)⁻¹ * ((s + s').factorial : ℝ)⁻¹ *
        ∑ primaryOrder : Equiv.Perm (Fin (r + r')), ∑ bodyOrder : Equiv.Perm (Fin (s + s')),
          _root_.CurrentAFT.ControlProduct.finDisjointTensor first.val second.val (colors ∘ primaryOrder) (centers ∘ bodyOrder) := by
  exact (_root_.CurrentAFT.ControlProduct.symmetrize_apply (_root_.CurrentAFT.ControlProduct.finDisjointTensor first.val second.val) colors centers).trans (by
    simp only [Fintype.card_perm, Fintype.card_fin])
open _root_.P2M60f02c0e renaming h25 → _p2mH25
end
open _root_.P2M60f02c0e renaming h25 → _p2mH25
end CurrentAFT.ControlProduct
open _root_.P2M60f02c0e renaming h25 → _p2mH25
end
open _root_.P2M60f02c0e renaming h25 → _p2mH25
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.dependentPolynomial
end AFT.RepresentedPolynomial.dependentPolynomial
namespace CurrentAFT.ControlProduct
end CurrentAFT.ControlProduct
namespace CurrentAFT.ControlProduct.disjointTensor
end CurrentAFT.ControlProduct.disjointTensor
namespace CurrentAFT.ControlProduct.finBlockSwap
end CurrentAFT.ControlProduct.finBlockSwap
namespace CurrentAFT.ControlProduct.finDisjointTensor
end CurrentAFT.ControlProduct.finDisjointTensor
namespace CurrentAFT.ControlProduct.finLeftUnit
end CurrentAFT.ControlProduct.finLeftUnit
namespace CurrentAFT.ControlProduct.finRightUnit
end CurrentAFT.ControlProduct.finRightUnit
namespace CurrentAFT.ControlProduct.reindexKernel
end CurrentAFT.ControlProduct.reindexKernel
namespace CurrentAFT.ControlProduct.scalarUnit
end CurrentAFT.ControlProduct.scalarUnit
namespace CurrentAFT.ControlProduct.symmetrize
end CurrentAFT.ControlProduct.symmetrize
namespace CurrentAFT.ControlProduct.truncatedHomogeneousProduct
end CurrentAFT.ControlProduct.truncatedHomogeneousProduct
section
namespace CurrentAFT.CanonicalReconstruction
open AFT ControlCoordinates ControlProduct
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.CanonicalReconstruction.classicalFinDecidableEq
variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]
set_option maxRecDepth 8192
private theorem _root_.P2M60f02c0e.h260 {Color : Type*} [Fintype Color] (law : _root_.AFT.FiniteDist Color)
    (hpositive : ∀ color, 0 < law.weight color) (source output : Color) :
    law.weight source * _root_.AFT.Hoeffding.centeredAtom law source output =
      (if output = source then 1 else 0) - law.weight source := by
  by_cases hequal : source = output
  · subst output
    simp only [_root_.AFT.Hoeffding.centeredAtom, if_true, mul_sub, mul_one,
      mul_inv_cancel₀ (hpositive source).ne']
  · simp only [_root_.AFT.Hoeffding.centeredAtom, hequal, Ne.symm hequal, if_false, zero_sub, mul_neg, mul_one]
open _root_.P2M60f02c0e renaming h260 → _p2mH260
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h24 {Color : Type*} [Fintype Color] (law : _root_.AFT.FiniteDist Color)
    (hpositive : ∀ color, 0 < law.weight color) {Index : Type*} [Fintype Index] [DecidableEq Index]
    (source output : Index → Color) :
    (∏ index, law.weight (source index)) *
        (∏ index, _root_.AFT.Hoeffding.centeredAtom law (source index) (output index)) =
      _root_.AFT.MixedKernel.canonicalPointBasis (fun _ : Index => law) source output := by
  rw [← Finset.prod_mul_distrib]
  simp only [_p2mH260 law hpositive, _root_.AFT.MixedKernel.canonicalPointBasis]
open _root_.P2M60f02c0e renaming h24 → _p2mH24
end
open _root_.P2M60f02c0e renaming h24 → _p2mH24
open _root_.P2M60f02c0e renaming h260 → _p2mH260
end CurrentAFT.CanonicalReconstruction
open _root_.P2M60f02c0e renaming h24 → _p2mH24
open _root_.P2M60f02c0e renaming h260 → _p2mH260
end
open _root_.P2M60f02c0e renaming h24 → _p2mH24
namespace CurrentAFT.ConditionalPairMean
end CurrentAFT.ConditionalPairMean
namespace CurrentAFT.ConditionalPairMean.centeredMean
end CurrentAFT.ConditionalPairMean.centeredMean
namespace CurrentAFT.ConditionalPairMean.diffuseFirst
end CurrentAFT.ConditionalPairMean.diffuseFirst
namespace CurrentAFT.ConditionalPairMean.diffuseSecond
end CurrentAFT.ConditionalPairMean.diffuseSecond
namespace CurrentAFT.ConditionalPairMean.firstMarginal
end CurrentAFT.ConditionalPairMean.firstMarginal
namespace CurrentAFT.ConditionalPairMean.markedSecond
end CurrentAFT.ConditionalPairMean.markedSecond
namespace CurrentAFT.ConditionalPairMean.pairMean
end CurrentAFT.ConditionalPairMean.pairMean
namespace CurrentAFT.ConditionalPairMean.secondMarginal
end CurrentAFT.ConditionalPairMean.secondMarginal
namespace CurrentAFT.LocalReferenceEnergy
end CurrentAFT.LocalReferenceEnergy
namespace CurrentAFT.LocalReferenceEnergy.markedPairAt
end CurrentAFT.LocalReferenceEnergy.markedPairAt
namespace CurrentAFT.UniformBodyProfiles
end CurrentAFT.UniformBodyProfiles
namespace CurrentAFT.UniformBodyProfiles.BodyRole
end CurrentAFT.UniformBodyProfiles.BodyRole
namespace CurrentAFT.UniformBodyProfiles.BodyRole.attachment
end CurrentAFT.UniformBodyProfiles.BodyRole.attachment
namespace CurrentAFT.UniformBodyProfiles.BodyRole.free
end CurrentAFT.UniformBodyProfiles.BodyRole.free
namespace CurrentAFT.UniformBodyProfiles.BodyRole.queue
end CurrentAFT.UniformBodyProfiles.BodyRole.queue
namespace CurrentAFT.UniformBodyProfiles.preRootLaw
end CurrentAFT.UniformBodyProfiles.preRootLaw
namespace CurrentAFT.UniformBodyProfiles.preRootLaw.match_1
end CurrentAFT.UniformBodyProfiles.preRootLaw.match_1
namespace CurrentAFT.UniformBodyProfiles.uniformVector
end CurrentAFT.UniformBodyProfiles.uniformVector
section
namespace CurrentAFT.BodyRootAverages
open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy FirstHistogram
  UniformBodyProfiles BackgroundCertificates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ProposalPrimary.centerLaw
  ProposalPrimary.safeLaw
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h20 (security : ℕ) (law : _root_.AFT.FiniteDist (_root_.CurrentAFT.LocalReferenceEnergy.Palette security)) :
    _root_.CurrentAFT.BodyRootAverages.rootAverage security law = (_root_.CurrentAFT.DiffuseProfiles.actualSeedLaw security).mix
      (fun seed => law.map (_root_.CurrentAFT.ProposalPrimary.shiftEquiv security (_root_.CurrentAFT.DiffuseProfiles.actualBlur security seed))) := by
  ext output
  simp only [_root_.CurrentAFT.BodyRootAverages.rootAverage, _root_.CurrentAFT.LocalReferenceEnergy.publicBlurLaw, _root_.CurrentAFT.DiffuseProfiles.actualSeedLaw, _root_.AFT.FiniteDist.mix_weight,
    Fintype.sum_prod_type, _root_.AFT.FiniteDist.prod_weight, _root_.AFT.FiniteDist.map_equiv_weight,
    _root_.CurrentAFT.DiffuseProfiles.actualBlur]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, _root_.AFT.FiniteDist.sum_one, one_mul]
  ring
open _root_.P2M60f02c0e renaming h20 → _p2mH20
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h19 (security : ℕ) :
    _root_.CurrentAFT.BodyRootAverages.rootAverage security (_root_.CurrentAFT.ProposalPrimary.centerLaw security) = _root_.CurrentAFT.BackgroundCertificates.convolvedCenterLaw security :=
  _p2mH20 security (_root_.CurrentAFT.ProposalPrimary.centerLaw security)
open _root_.P2M60f02c0e renaming h19 → _p2mH19
end
open _root_.P2M60f02c0e renaming h19 → _p2mH19
open _root_.P2M60f02c0e renaming h20 → _p2mH20
end CurrentAFT.BodyRootAverages
open _root_.P2M60f02c0e renaming h19 → _p2mH19
open _root_.P2M60f02c0e renaming h20 → _p2mH20
end
open _root_.P2M60f02c0e renaming h19 → _p2mH19
open _root_.P2M60f02c0e renaming h20 → _p2mH20
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.expectation
end AFT.FiniteDist.expectation
namespace AFT.FiniteDist.independent
end AFT.FiniteDist.independent
namespace AFT.FiniteDist.l2Sq
end AFT.FiniteDist.l2Sq
namespace AFT.FiniteDist.mk
end AFT.FiniteDist.mk
namespace AFT.FiniteDist.normalize
end AFT.FiniteDist.normalize
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.windowGaussian
end AFT.GaussianSource.windowGaussian
namespace AFT.GaussianSource.windowNegate
end AFT.GaussianSource.windowNegate
namespace AFT.GaussianSource.windowNormalizer
end AFT.GaussianSource.windowNormalizer
namespace AFT.GaussianSource.windowZero
end AFT.GaussianSource.windowZero
namespace AFT.Hoeffding
end AFT.Hoeffding
namespace AFT.Hoeffding.centeredAtom
end AFT.Hoeffding.centeredAtom
namespace AFT.Hoeffding.densityComponent
end AFT.Hoeffding.densityComponent
namespace AFT.RootSlice
end AFT.RootSlice
namespace CurrentAFT.PublicCharge
end CurrentAFT.PublicCharge
namespace CurrentAFT.PublicCharge.assembledEndpoint
end CurrentAFT.PublicCharge.assembledEndpoint
namespace CurrentAFT.PublicCharge.assembledEndpoint.match_1
end CurrentAFT.PublicCharge.assembledEndpoint.match_1
namespace CurrentAFT.PublicCharge.cycleDifference
end CurrentAFT.PublicCharge.cycleDifference
namespace CurrentAFT.PublicCharge.legCompanion
end CurrentAFT.PublicCharge.legCompanion
namespace CurrentAFT.PublicCharge.queueIncrement
end CurrentAFT.PublicCharge.queueIncrement
namespace CurrentAFT.characterFourier
end CurrentAFT.characterFourier
namespace CurrentAFT.coordinateCharacter
end CurrentAFT.coordinateCharacter
namespace CurrentAFT.signedFourier
end CurrentAFT.signedFourier
namespace CurrentAFT.uniformDensity
end CurrentAFT.uniformDensity
namespace CurrentAFT.uniformDeviation
end CurrentAFT.uniformDeviation
section
namespace CurrentAFT.ProtectedCycle
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h83 {Index Scalar : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype Scalar]
    (reference : Index → _root_.AFT.FiniteDist Scalar) (first second : Index) (hdistinct : second ≠ first) :
    (_root_.AFT.FiniteDist.independent reference).map (fun latent => (latent first, latent second)) =
      (reference first).prod (reference second) := by
  ext values
  have htest := _root_.CurrentAFT.ProtectedCycle.independent_pair_expectation reference first second hdistinct
    (fun firstValue secondValue => if (firstValue, secondValue) = values then 1 else 0)
  have hleft : (_root_.AFT.FiniteDist.independent reference).expectation
      (fun latent => if (latent first, latent second) = values then 1 else 0) =
      ((_root_.AFT.FiniteDist.independent reference).map
        (fun latent => (latent first, latent second))).weight values := by
    simp only [_root_.AFT.FiniteDist.expectation, _root_.AFT.FiniteDist.map_weight, mul_ite, mul_one, mul_zero]
    apply Finset.sum_congr rfl
    intro latent _
    by_cases hequal : (latent first, latent second) = values <;> simp [hequal]
  rw [hleft] at htest
  rw [htest]
  rcases values with ⟨firstValue, secondValue⟩
  simp [mul_ite, _root_.AFT.FiniteDist.prod_weight, ite_and]
open _root_.P2M60f02c0e renaming h83 → _p2mH83
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h81 {Scalar : Type*} [Fintype Scalar]
    (body modulus : ℕ) [NeZero modulus] (edgeLaw : _root_.AFT.FiniteDist Scalar)
    (value : Scalar → ZMod modulus) (vertex : Fin body)
    (hdistinct : (finRotate body).symm vertex ≠ vertex) :
    (_root_.CurrentAFT.ProtectedCycle.cycleLaw body modulus edgeLaw value).map (fun root => root vertex) =
      _root_.CurrentAFT.ProtectedCycle.differenceLaw edgeLaw value := by
  unfold _root_.CurrentAFT.ProtectedCycle.cycleLaw _root_.CurrentAFT.ProtectedCycle.differenceLaw
  rw [_root_.AFT.FiniteDist.map_map]
  have hpair := _p2mH83 (fun _ : Fin body => edgeLaw) vertex
    ((finRotate body).symm vertex) hdistinct
  rw [← hpair, _root_.AFT.FiniteDist.map_map]
  rfl
open _root_.P2M60f02c0e renaming h81 → _p2mH81
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h82 {Scalar : Type*} [Fintype Scalar]
    (body modulus : ℕ) [NeZero modulus] (edgeLaw : _root_.AFT.FiniteDist Scalar)
    (value : Scalar → ZMod modulus) (hbody : 2 ≤ body) (vertex : Fin body) :
    (_root_.CurrentAFT.ProtectedCycle.cycleLaw body modulus edgeLaw value).map (fun root => root vertex) =
      _root_.CurrentAFT.ProtectedCycle.differenceLaw edgeLaw value :=
  _p2mH81 body modulus edgeLaw value vertex (_root_.CurrentAFT.ProtectedCycle.cycle_predecessor_ne body hbody vertex)
open _root_.P2M60f02c0e renaming h82 → _p2mH82
end
open _root_.P2M60f02c0e renaming h81 → _p2mH81
open _root_.P2M60f02c0e renaming h82 → _p2mH82
open _root_.P2M60f02c0e renaming h83 → _p2mH83
end CurrentAFT.ProtectedCycle
open _root_.P2M60f02c0e renaming h81 → _p2mH81
open _root_.P2M60f02c0e renaming h82 → _p2mH82
open _root_.P2M60f02c0e renaming h83 → _p2mH83
end
open _root_.P2M60f02c0e renaming h81 → _p2mH81
open _root_.P2M60f02c0e renaming h82 → _p2mH82
open _root_.P2M60f02c0e renaming h83 → _p2mH83
namespace CurrentAFT.PathLikelihood
end CurrentAFT.PathLikelihood
namespace CurrentAFT.PathLikelihood.amplitude
end CurrentAFT.PathLikelihood.amplitude
namespace CurrentAFT.PathLikelihood.amplitude.match_1
end CurrentAFT.PathLikelihood.amplitude.match_1
namespace CurrentAFT.PathLikelihood.latentLaw
end CurrentAFT.PathLikelihood.latentLaw
namespace CurrentAFT.PathLikelihood.marginal
end CurrentAFT.PathLikelihood.marginal
namespace CurrentAFT.PathLikelihood.pathKernel
end CurrentAFT.PathLikelihood.pathKernel
namespace CurrentAFT.PathLikelihood.pathKernel.match_1
end CurrentAFT.PathLikelihood.pathKernel.match_1
namespace CurrentAFT.PathLikelihood.pathLaw
end CurrentAFT.PathLikelihood.pathLaw
namespace CurrentAFT.PathLikelihood.pathOutput
end CurrentAFT.PathLikelihood.pathOutput
namespace CurrentAFT.PathLikelihood.squareSum
end CurrentAFT.PathLikelihood.squareSum
namespace CurrentAFT.PathLikelihood.transfer
end CurrentAFT.PathLikelihood.transfer
namespace CurrentAFT.ProtectedCycle
end CurrentAFT.ProtectedCycle
namespace CurrentAFT.ProtectedCycle.centeredRelabeledCycleLaw
end CurrentAFT.ProtectedCycle.centeredRelabeledCycleLaw
section
namespace CurrentAFT.CycleSelections
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h33 {Scalar : Type*} [Fintype Scalar]
    (body order modulus : ℕ) [NeZero modulus] (hbody : 2 ≤ body)
    (source : _root_.AFT.FiniteDist Scalar) (value : Scalar → ZMod modulus)
    (sites : _root_.CurrentAFT.CycleSelections.Selection body order) (slot : Fin order) :
    (_root_.CurrentAFT.CycleSelections.selectedLaw body order modulus source value sites).map (fun root => root slot) =
      _root_.CurrentAFT.ProtectedCycle.differenceLaw source value := by
  rw [_root_.CurrentAFT.CycleSelections.selectedLaw, _root_.AFT.FiniteDist.map_map]
  exact _p2mH82 body modulus source value hbody (sites slot)
open _root_.P2M60f02c0e renaming h33 → _p2mH33
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h32 {Scalar : Type*} [Fintype Scalar]
    (body order modulus : ℕ) [NeZero modulus] (horder : order ≤ body) (hbody : 2 ≤ body)
    (source : _root_.AFT.FiniteDist Scalar) (value : Scalar → ZMod modulus) (slot : Fin order) :
    (_root_.CurrentAFT.CycleSelections.averagedSelectedLaw body order modulus horder source value).map (fun root => root slot) =
      _root_.CurrentAFT.ProtectedCycle.differenceLaw source value := by
  rw [_root_.CurrentAFT.CycleSelections.averagedSelectedLaw, _root_.AFT.FiniteDist.map_mix]
  simp_rw [_p2mH33 body order modulus hbody source value]
  exact _root_.AFT.FiniteDist.mix_const _ _
open _root_.P2M60f02c0e renaming h32 → _p2mH32
end
open _root_.P2M60f02c0e renaming h32 → _p2mH32
open _root_.P2M60f02c0e renaming h33 → _p2mH33
end CurrentAFT.CycleSelections
open _root_.P2M60f02c0e renaming h32 → _p2mH32
open _root_.P2M60f02c0e renaming h33 → _p2mH33
end
open _root_.P2M60f02c0e renaming h32 → _p2mH32
open _root_.P2M60f02c0e renaming h33 → _p2mH33
namespace CurrentAFT.CycleSelections
end CurrentAFT.CycleSelections
namespace CurrentAFT.CycleSelections.averagedSelectedLaw
end CurrentAFT.CycleSelections.averagedSelectedLaw
namespace CurrentAFT.CycleSelections.currentRootTag
end CurrentAFT.CycleSelections.currentRootTag
namespace CurrentAFT.CycleSelections.selectionPermutation
end CurrentAFT.CycleSelections.selectionPermutation
namespace CurrentAFT.SupportedHoeffding
end CurrentAFT.SupportedHoeffding
section
namespace CurrentAFT.CycleRootExpansion
open AFT CycleSelections
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {Index Color Value : Type*} [Fintype Index] [DecidableEq Index] [Fintype Color]
  [AddCommGroup Value] [Module ℝ Value]
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h30 (joint : _root_.AFT.FiniteDist (Index → Color))
    (reference : Index → _root_.AFT.FiniteDist Color)
    (hmarginal : ∀ index, joint.map (fun word => word index) = reference index)
    (word : Index → Color) (hword : joint.weight word ≠ 0) (index : Index) :
    0 < (reference index).weight (word index) := by
  have hpositive : 0 < joint.weight word := lt_of_le_of_ne (joint.nonneg word) (Ne.symm hword)
  rw [← hmarginal index, _root_.AFT.FiniteDist.map_weight]
  apply hpositive.trans_le
  apply (Finset.single_le_sum (s := Finset.univ)
    (f := fun input => if input index = word index then joint.weight input else 0)
    (fun input _ => by split_ifs; exact joint.nonneg input; exact le_rfl)
    (Finset.mem_univ word)).trans'
  simp only [if_true, le_refl]
open _root_.P2M60f02c0e renaming h30 → _p2mH30
section Actual
attribute [local instance] _root_.CurrentAFT.CycleRootExpansion.currentModulusNeZero
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h29 (security : ℕ) : 2 ≤ _root_.CurrentAFT.Parameters.bodySize security := by
  have hbase := _root_.CurrentAFT.Parameters.base_ge_two security
  have hmod := (_root_.CurrentAFT.Parameters.modulus_spec security).2.two_le
  have hpower : 1 ≤ _root_.CurrentAFT.Parameters.base security ^ 96 := one_le_pow₀ (by omega)
  rw [_root_.CurrentAFT.Parameters.bodySize_eq]
  exact hmod.trans (by simpa using Nat.mul_le_mul_left (_root_.CurrentAFT.Parameters.modulus security) hpower)
open _root_.P2M60f02c0e renaming h29 → _p2mH29
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h31 (security : ℕ) (index : _root_.CurrentAFT.CycleRootExpansion.Vertex security) :
    (_root_.CurrentAFT.CycleRootExpansion.rootLaw security).map (fun roots => roots index) = _root_.CurrentAFT.CycleRootExpansion.rootReference security := by
  let labels : _root_.CurrentAFT.CycleSelections.Selection (_root_.CurrentAFT.Parameters.bodySize security) 1 :=
    ⟨fun _ => index, fun first second _ => Subsingleton.elim first second⟩
  have h := congrArg (fun law : _root_.AFT.FiniteDist (Fin 1 → _root_.CurrentAFT.CycleRootExpansion.Root security) =>
    law.map (fun roots => roots 0))
    (_root_.CurrentAFT.CycleRootExpansion.rootLaw_selected security 1 (by have := _p2mH29 security; omega) labels)
  rw [_root_.AFT.FiniteDist.map_map] at h
  exact h.trans (_p2mH32 _ _ _ _
    (_p2mH29 security) _ _ 0)
open _root_.P2M60f02c0e renaming h31 → _p2mH31
variable {Control : Type*} [Fintype Control]
end Actual
open _root_.P2M60f02c0e renaming h29 → _p2mH29
open _root_.P2M60f02c0e renaming h31 → _p2mH31
end
open _root_.P2M60f02c0e renaming h29 → _p2mH29
open _root_.P2M60f02c0e renaming h30 → _p2mH30
open _root_.P2M60f02c0e renaming h31 → _p2mH31
end CurrentAFT.CycleRootExpansion
open _root_.P2M60f02c0e renaming h29 → _p2mH29
open _root_.P2M60f02c0e renaming h30 → _p2mH30
open _root_.P2M60f02c0e renaming h31 → _p2mH31
end
open _root_.P2M60f02c0e renaming h29 → _p2mH29
open _root_.P2M60f02c0e renaming h30 → _p2mH30
open _root_.P2M60f02c0e renaming h31 → _p2mH31
namespace CurrentAFT.ActualBlockFock
end CurrentAFT.ActualBlockFock
namespace CurrentAFT.ActualBlockFock.blockLawAt
end CurrentAFT.ActualBlockFock.blockLawAt
namespace CurrentAFT.ActualBlockFock.blockLawAt.match_1
end CurrentAFT.ActualBlockFock.blockLawAt.match_1
namespace CurrentAFT.BackgroundPolynomialEvaluation
end CurrentAFT.BackgroundPolynomialEvaluation
namespace CurrentAFT.BackgroundPolynomialEvaluation.finiteGenerating
end CurrentAFT.BackgroundPolynomialEvaluation.finiteGenerating
namespace CurrentAFT.RootBackgroundPolynomial
end CurrentAFT.RootBackgroundPolynomial
namespace CurrentAFT.RootBackgroundPolynomial.localPolynomialInt
end CurrentAFT.RootBackgroundPolynomial.localPolynomialInt
namespace CurrentAFT.RootBackgroundPolynomial.localPolynomialInt.match_1
end CurrentAFT.RootBackgroundPolynomial.localPolynomialInt.match_1
namespace CurrentAFT.RootBackgroundPolynomial.rootedResidues
end CurrentAFT.RootBackgroundPolynomial.rootedResidues
section
namespace CurrentAFT.RootIndependentBackground
open AFT AFT.RepresentedPolynomial DiffuseProfiles ProposalPrimary ActualControls
  LocalReferenceEnergy ActualBlockFock ActualBlockMean ActualCycleMeanMGF
  BackgroundPolynomialEvaluation BackgroundEndpointLaw RootBackgroundPolynomial
  CycleRootExpansion CycleRootPolynomial BodyRootAverages PairQuadraticEvaluation
  PositiveFirstCoefficient LegPolynomialEvaluation BackgroundTranslations
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
  CycleRootExpansion.rootLaw CycleRootExpansion.rootReference
attribute [local instance] _root_.CurrentAFT.RootIndependentBackground.finOneDecidableEq
attribute [local instance] _root_.CurrentAFT.RootIndependentBackground.finThreeDecidableEq
attribute [local instance] _root_.CurrentAFT.RootIndependentBackground.blockIndexDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h209 {Input Output State : Type*} [Fintype Input] [Fintype Output] [Fintype State]
    (law : _root_.AFT.FiniteDist Input) (map : Input → Output) (kernel : Output → _root_.AFT.FiniteDist State) :
    (law.map map).mix kernel = law.mix (kernel ∘ map) := by
  ext state
  change (law.map map).expectation (fun output => (kernel output).weight state) =
    law.expectation (fun input => (kernel (map input)).weight state)
  rw [_root_.AFT.FiniteDist.expectation_map]
  rfl
open _root_.P2M60f02c0e renaming h209 → _p2mH209
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h210 (security : ℕ) (law : _root_.AFT.FiniteDist (_root_.CurrentAFT.ActualControls.Palette security)) :
    (_root_.CurrentAFT.CycleRootExpansion.rootReference security).mix (fun root => law.map (_root_.CurrentAFT.ProposalPrimary.shiftEquiv security (root.val : ℤ))) =
      _root_.CurrentAFT.BodyRootAverages.rootAverage security law := by
  unfold _root_.CurrentAFT.CycleRootExpansion.rootReference _root_.CurrentAFT.ProtectedCycle.differenceLaw
  rw [_p2mH209]
  have hshift (edge : _root_.CurrentAFT.LocalReferenceEnergy.BlurSeed security) :
      _root_.CurrentAFT.ProposalPrimary.shiftEquiv security
        (((((edge.1 : ℤ) : _root_.CurrentAFT.CycleRootExpansion.Root security) - ((edge.2 : ℤ) : _root_.CurrentAFT.CycleRootExpansion.Root security)).val : ℕ) : ℤ) =
        _root_.CurrentAFT.ProposalPrimary.shiftEquiv security (edge.1.val - edge.2.val) := by
    apply _root_.CurrentAFT.RootBackgroundPolynomial.shiftEquiv_eq_of_cast
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val, Int.cast_sub]
  ext output
  simp only [_root_.AFT.FiniteDist.mix_weight, Function.comp_apply, hshift,
    _root_.CurrentAFT.BodyRootAverages.rootAverage, _root_.CurrentAFT.LocalReferenceEnergy.publicBlurLaw, Fintype.sum_prod_type, _root_.AFT.FiniteDist.prod_weight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  ring
open _root_.P2M60f02c0e renaming h210 → _p2mH210
end
open _root_.P2M60f02c0e renaming h209 → _p2mH209
open _root_.P2M60f02c0e renaming h210 → _p2mH210
end CurrentAFT.RootIndependentBackground
open _root_.P2M60f02c0e renaming h209 → _p2mH209
open _root_.P2M60f02c0e renaming h210 → _p2mH210
end
open _root_.P2M60f02c0e renaming h209 → _p2mH209
open _root_.P2M60f02c0e renaming h210 → _p2mH210
namespace AFT.TensorChannel
end AFT.TensorChannel
namespace AFT.TensorChannel.applyLinear
end AFT.TensorChannel.applyLinear
namespace AFT.TensorChannel.center
end AFT.TensorChannel.center
section
namespace CurrentAFT.RootCoordinateProjection
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable {Index Root Control : Type*} [Fintype Index] [DecidableEq Index]
  [Fintype Root] [Fintype Control]
set_option maxRecDepth 8192
omit [Fintype Index] [Fintype Control] in
theorem _root_.P2M60f02c0e.h206 (root : _root_.AFT.FiniteDist Root) (index : Index)
    (score : _root_.CurrentAFT.RootCoordinateProjection.Input (Index := Index) (Root := Root) (Control := Control) → ℝ)
    (hinvariant : ∀ sample value, score (Function.update sample.1 index value, sample.2) = score sample) :
    _root_.CurrentAFT.RootCoordinateProjection.average root index score = score := by
  funext sample
  simp only [_root_.CurrentAFT.RootCoordinateProjection.average_apply, hinvariant, _root_.AFT.FiniteDist.expectation_const]
open _root_.P2M60f02c0e renaming h206 → _p2mH206
set_option maxRecDepth 8192
omit [Fintype Index] [Fintype Control] in
theorem _root_.P2M60f02c0e.h207 (root : _root_.AFT.FiniteDist Root) (index : Index)
    (score : _root_.CurrentAFT.RootCoordinateProjection.Input (Index := Index) (Root := Root) (Control := Control) → ℝ)
    (hcentered : ∀ sample : _root_.CurrentAFT.RootCoordinateProjection.Input (Index := Index) (Root := Root) (Control := Control), root.expectation (fun value => score (Function.update sample.1 index value, sample.2)) = 0) :
    _root_.CurrentAFT.RootCoordinateProjection.center root index score = score := by
  funext sample
  simp only [_root_.CurrentAFT.RootCoordinateProjection.center_apply, _root_.CurrentAFT.RootCoordinateProjection.average_apply, hcentered, sub_zero]
open _root_.P2M60f02c0e renaming h207 → _p2mH207
set_option maxRecDepth 8192
omit [Fintype Index] [Fintype Control] in
theorem _root_.P2M60f02c0e.h208 (root : _root_.AFT.FiniteDist Root) (coordinates : List (Index × Bool))
    (score : _root_.CurrentAFT.RootCoordinateProjection.Input (Index := Index) (Root := Root) (Control := Control) → ℝ)
    (hfixed : ∀ item ∈ coordinates, _root_.CurrentAFT.RootCoordinateProjection.coordinate root item.1 item.2 score = score) :
    _root_.CurrentAFT.RootCoordinateProjection.sequence root coordinates score = score := by
  induction coordinates with
  | nil => rfl
  | cons item rest ih =>
    change _root_.CurrentAFT.RootCoordinateProjection.coordinate root item.1 item.2 (_root_.CurrentAFT.RootCoordinateProjection.sequence root rest score) = score
    rw [ih (fun other hother => hfixed other (List.mem_cons_of_mem item hother))]
    exact hfixed item List.mem_cons_self
open _root_.P2M60f02c0e renaming h208 → _p2mH208
end
open _root_.P2M60f02c0e renaming h206 → _p2mH206
open _root_.P2M60f02c0e renaming h207 → _p2mH207
open _root_.P2M60f02c0e renaming h208 → _p2mH208
end CurrentAFT.RootCoordinateProjection
open _root_.P2M60f02c0e renaming h206 → _p2mH206
open _root_.P2M60f02c0e renaming h207 → _p2mH207
open _root_.P2M60f02c0e renaming h208 → _p2mH208
end
open _root_.P2M60f02c0e renaming h206 → _p2mH206
open _root_.P2M60f02c0e renaming h207 → _p2mH207
open _root_.P2M60f02c0e renaming h208 → _p2mH208
namespace CurrentAFT.LocalReferenceEnergy.tripleMassAt
end CurrentAFT.LocalReferenceEnergy.tripleMassAt
namespace CurrentAFT.PrimaryMassFamilies
end CurrentAFT.PrimaryMassFamilies
namespace CurrentAFT.PrimaryMassFamilies.massCertificateFamily
end CurrentAFT.PrimaryMassFamilies.massCertificateFamily
namespace CurrentAFT.PrimaryMassFamilies.massLiftKernel
end CurrentAFT.PrimaryMassFamilies.massLiftKernel
namespace CurrentAFT.PrimaryMassFamilies.oneWordProfile
end CurrentAFT.PrimaryMassFamilies.oneWordProfile
namespace CurrentAFT.PrimaryMassFamilies.pairWordProfile
end CurrentAFT.PrimaryMassFamilies.pairWordProfile
namespace CurrentAFT.PrimaryMassFamilies.primaryArity
end CurrentAFT.PrimaryMassFamilies.primaryArity
namespace CurrentAFT.RootIndependentBackground
end CurrentAFT.RootIndependentBackground
namespace CurrentAFT.RootIndependentBackground.roleMeanPolynomial
end CurrentAFT.RootIndependentBackground.roleMeanPolynomial
namespace CurrentAFT.RootIndependentBackground.roleMeanPolynomial.match_1
end CurrentAFT.RootIndependentBackground.roleMeanPolynomial.match_1
namespace CurrentAFT.RootIndependentBackground.tripleEquiv
end CurrentAFT.RootIndependentBackground.tripleEquiv
section
namespace CurrentAFT.RootTaggedLocal
open AFT DiffuseProfiles ProposalPrimary ActualControls LocalReferenceEnergy
  UniformBodyProfiles CycleRootExpansion RootBackgroundPolynomial PrimaryTensorInverse
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize ProposalPrimary.primaryLaw
  CycleRootExpansion.rootReference
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h249 (security : ℕ) (role : _root_.CurrentAFT.UniformBodyProfiles.BodyRole) (queue : ℤ) (color : _root_.CurrentAFT.ActualControls.Palette security) :
    (_root_.CurrentAFT.CycleRootExpansion.rootReference security).expectation (fun root => _root_.CurrentAFT.RootTaggedLocal.deviationProfile security role queue root color) = 0 := by
  simp only [_root_.AFT.FiniteDist.expectation, _root_.CurrentAFT.RootTaggedLocal.deviationProfile, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul, _root_.AFT.FiniteDist.sum_one, one_mul, _root_.CurrentAFT.RootTaggedLocal.meanLaw, _root_.AFT.FiniteDist.mix_weight, sub_self]
open _root_.P2M60f02c0e renaming h249 → _p2mH249
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h251 (security : ℕ) (role : _root_.CurrentAFT.UniformBodyProfiles.BodyRole) (queue : ℤ) :
    _root_.CurrentAFT.RootTaggedLocal.rootMass security role queue (fun _ => 1) = 0 := by
  funext color
  simpa only [_root_.CurrentAFT.RootTaggedLocal.rootMass, LinearMap.coe_mk, AddHom.coe_mk, mul_one, _root_.AFT.FiniteDist.expectation, Pi.zero_apply] using
    _p2mH249 security role queue color
open _root_.P2M60f02c0e renaming h251 → _p2mH251
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h250 (security : ℕ) (role : _root_.CurrentAFT.UniformBodyProfiles.BodyRole) (queue : ℤ) :
    _root_.CurrentAFT.RootTaggedLocal.rootLift security role queue (fun _ => 1) = 0 := by
  rw [_root_.CurrentAFT.RootTaggedLocal.rootLift_apply, _p2mH251, map_zero, map_zero]
open _root_.P2M60f02c0e renaming h250 → _p2mH250
end
open _root_.P2M60f02c0e renaming h249 → _p2mH249
open _root_.P2M60f02c0e renaming h250 → _p2mH250
open _root_.P2M60f02c0e renaming h251 → _p2mH251
end CurrentAFT.RootTaggedLocal
open _root_.P2M60f02c0e renaming h249 → _p2mH249
open _root_.P2M60f02c0e renaming h250 → _p2mH250
open _root_.P2M60f02c0e renaming h251 → _p2mH251
end
open _root_.P2M60f02c0e renaming h249 → _p2mH249
open _root_.P2M60f02c0e renaming h250 → _p2mH250
open _root_.P2M60f02c0e renaming h251 → _p2mH251
namespace CurrentAFT.RootTaggedLocal
end CurrentAFT.RootTaggedLocal
namespace CurrentAFT.RootTaggedLocal.deviationProfile
end CurrentAFT.RootTaggedLocal.deviationProfile
namespace CurrentAFT.RootTaggedLocal.meanLaw
end CurrentAFT.RootTaggedLocal.meanLaw
namespace CurrentAFT.RootTaggedLocal.rootCost
end CurrentAFT.RootTaggedLocal.rootCost
namespace CurrentAFT.RootTaggedLocal.rootMass
end CurrentAFT.RootTaggedLocal.rootMass
namespace CurrentAFT.RootTaggedLocal.shiftedLaw
end CurrentAFT.RootTaggedLocal.shiftedLaw
section
namespace CurrentAFT.RootTaggedFamilies
open AFT ControlCoordinates GradedControlAlgebra GradedControlNorm DiffuseProfiles
  ProposalPrimary ActualControls UniformBodyProfiles CycleRootExpansion RootTaggedLocal
  BackgroundFamilies BackgroundRates BackgroundEvaluation BackgroundFirstEvaluation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize ProposalPrimary.primaryLaw
  ActualControls.bodyReference CycleRootExpansion.rootReference
attribute [local instance] _root_.CurrentAFT.RootTaggedFamilies.classicalFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h247 (security order : ℕ) (horder : 1 ≤ order) (role : _root_.CurrentAFT.UniformBodyProfiles.BodyRole) (queue : ℤ) :
    _root_.CurrentAFT.RootTaggedFamilies.rootFamilyLinear security order horder role queue (fun _ => 1) = 0 := by
  funext arity
  by_cases hequal : arity = _root_.CurrentAFT.BackgroundFamilies.primaryArity order horder
  · subst arity
    simp only [_root_.CurrentAFT.RootTaggedFamilies.rootFamilyLinear, LinearMap.comp_apply, LinearMap.single_apply, Pi.single_eq_same, Pi.zero_apply]
    change _root_.CurrentAFT.RootTaggedFamilies.rootKernelLinear security role queue (fun _ => 1) = 0
    apply Subtype.ext
    funext colors centers
    exact congrFun (_p2mH250 security role queue) (colors 0)
  · simp only [_root_.CurrentAFT.RootTaggedFamilies.rootFamilyLinear, LinearMap.comp_apply, LinearMap.single_apply, Pi.zero_apply]
    exact Pi.single_eq_of_ne (M := fun arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order =>
      _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) arity.val.1.val arity.val.2.val) hequal _
open _root_.P2M60f02c0e renaming h247 → _p2mH247
end
open _root_.P2M60f02c0e renaming h247 → _p2mH247
end CurrentAFT.RootTaggedFamilies
open _root_.P2M60f02c0e renaming h247 → _p2mH247
end
open _root_.P2M60f02c0e renaming h247 → _p2mH247
namespace CurrentAFT.LocalCoefficientNorm
end CurrentAFT.LocalCoefficientNorm
namespace CurrentAFT.LocalCoefficientNorm.primaryMassEnergy
end CurrentAFT.LocalCoefficientNorm.primaryMassEnergy
namespace CurrentAFT.RootTaggedLegFirst
end CurrentAFT.RootTaggedLegFirst
namespace CurrentAFT.RootTaggedLegFirst.legFirstMass
end CurrentAFT.RootTaggedLegFirst.legFirstMass
namespace CurrentAFT.RootTaggedLegFirst.meanLegHistogram
end CurrentAFT.RootTaggedLegFirst.meanLegHistogram
section
namespace CurrentAFT.RootTaggedLegHigher
open AFT DiffuseProfiles ProposalPrimary ActualControls LocalReferenceEnergy
  ActualBlockFock PositiveFirstCoefficient CycleRootExpansion RootTaggedLocal
  PrimaryTensorInverse PhysicalBlockTensors BlockFock
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize ProposalPrimary.primaryLaw
  CycleRootExpansion.rootReference
attribute [local instance] _root_.CurrentAFT.RootTaggedLegHigher.finThreeDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h248 (security : ℕ) : _root_.CurrentAFT.RootTaggedLegHigher.massLinear security (fun _ => 1) = 0 := by
  have hcenter : _root_.AFT.TensorChannel.center (_root_.CurrentAFT.CycleRootExpansion.rootReference security) (fun _ => 1) = 0 := by
    funext root
    simp only [_root_.AFT.TensorChannel.center_apply, _root_.AFT.FiniteDist.expectation_const, sub_self, Pi.zero_apply]
  rw [_root_.CurrentAFT.RootTaggedLegHigher.massLinear, LinearMap.comp_apply, hcenter, map_zero]
open _root_.P2M60f02c0e renaming h248 → _p2mH248
end
open _root_.P2M60f02c0e renaming h248 → _p2mH248
end CurrentAFT.RootTaggedLegHigher
open _root_.P2M60f02c0e renaming h248 → _p2mH248
end
open _root_.P2M60f02c0e renaming h248 → _p2mH248
namespace CurrentAFT.CycleRootExpansion
end CurrentAFT.CycleRootExpansion
namespace CurrentAFT.CycleRootExpansion.componentResponse
end CurrentAFT.CycleRootExpansion.componentResponse
namespace CurrentAFT.CycleRootExpansion.expectationLinear
end CurrentAFT.CycleRootExpansion.expectationLinear
namespace CurrentAFT.CycleRootExpansion.rootLaw
end CurrentAFT.CycleRootExpansion.rootLaw
section
namespace CurrentAFT.SelectedRootComponent
open AFT CycleSelections CycleRootExpansion
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize
attribute [local instance] _root_.CurrentAFT.SelectedRootComponent.currentModulusNeZero
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h255 (security count : ℕ)
    (labels : _root_.CurrentAFT.CycleSelections.Selection (_root_.CurrentAFT.Parameters.bodySize security) count) (index : Fin count) :
    _root_.AFT.Hoeffding.CenteredAt (fun _ => _root_.CurrentAFT.CycleRootExpansion.rootReference security) index
      (_root_.CurrentAFT.CycleRootExpansion.selectedCoefficient security count labels) := by
  let joint := (_root_.CurrentAFT.CycleRootExpansion.rootLaw security).map (fun roots slot => roots (labels slot))
  have hmarginal (slot : Fin count) :
      joint.map (fun roots => roots slot) = _root_.CurrentAFT.CycleRootExpansion.rootReference security := by
    dsimp only [joint]
    rw [_root_.AFT.FiniteDist.map_map]
    exact _p2mH31 security (labels slot)
  have hcanonical := _root_.CurrentAFT.SupportedHoeffding.densityComponent_canonical_of_support
    (fun _ : Fin count => _root_.CurrentAFT.CycleRootExpansion.rootReference security) joint.weight
    (_p2mH30 joint (fun _ => _root_.CurrentAFT.CycleRootExpansion.rootReference security) hmarginal) Finset.univ
  have hequal : _root_.CurrentAFT.CycleRootExpansion.selectedCoefficient security count labels =
      _root_.AFT.Hoeffding.densityComponent (fun _ : Fin count => _root_.CurrentAFT.CycleRootExpansion.rootReference security) joint.weight Finset.univ := by
    funext word
    simp only [_root_.CurrentAFT.CycleRootExpansion.selectedCoefficient, _root_.CurrentAFT.CycleSelections.centeredRootDensity, _root_.AFT.FiniteDist.expectation,
      _root_.AFT.Hoeffding.densityComponent, _root_.CurrentAFT.SupportedHoeffding.centeredRootAtom_eq, joint]
    congr 3
    exact Subsingleton.elim _ _
  rw [hequal]
  exact hcanonical.2 index (Finset.mem_univ index)
open _root_.P2M60f02c0e renaming h255 → _p2mH255
end
open _root_.P2M60f02c0e renaming h255 → _p2mH255
end CurrentAFT.SelectedRootComponent
open _root_.P2M60f02c0e renaming h255 → _p2mH255
end
open _root_.P2M60f02c0e renaming h255 → _p2mH255
namespace CurrentAFT.PairedRootInput
end CurrentAFT.PairedRootInput
namespace CurrentAFT.PairedRootInput.controlKernel
end CurrentAFT.PairedRootInput.controlKernel
namespace CurrentAFT.PairedRootInput.controlReference
end CurrentAFT.PairedRootInput.controlReference
namespace CurrentAFT.PairedRootInput.controlReference.match_1
end CurrentAFT.PairedRootInput.controlReference.match_1
namespace CurrentAFT.PairedRootInput.jointInput
end CurrentAFT.PairedRootInput.jointInput
namespace CurrentAFT.PairedRootInput.labels
end CurrentAFT.PairedRootInput.labels
namespace CurrentAFT.PairedRootInput.sourceEmbedding
end CurrentAFT.PairedRootInput.sourceEmbedding
section
namespace CurrentAFT.PairedRootCentering
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  ControlCoordinates RaisingPatternBudget
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.PairedRootCentering.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.PairedRootCentering.classicalSumDecidableEq
attribute [local instance] _root_.CurrentAFT.PairedRootCentering.classicalSigmaDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h70 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (index : Fin tagged.card) :
    _root_.AFT.Hoeffding.CenteredAt (fun _ => _root_.CurrentAFT.CycleRootExpansion.rootReference security)
      (_root_.CurrentAFT.PairedRootInput.sourceEmbedding selection tagged index) (_root_.CurrentAFT.PairedRootCentering.rootDensity selection tagged layout) := by
  intro roots
  change (∑ root, (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight root *
    _root_.CurrentAFT.CycleRootExpansion.selectedCoefficient security tagged.card (_root_.CurrentAFT.PairedRootInput.labels tagged layout)
      (Function.update roots (_root_.CurrentAFT.PairedRootInput.sourceEmbedding selection tagged index) root ∘ _root_.CurrentAFT.PairedRootInput.sourceEmbedding selection tagged)) = 0
  simp_rw [Function.update_comp_eq_of_injective roots (_root_.CurrentAFT.PairedRootInput.sourceEmbedding selection tagged).injective]
  have h := _p2mH255 security tagged.card (_root_.CurrentAFT.PairedRootInput.labels tagged layout) index
  convert h (roots ∘ _root_.CurrentAFT.PairedRootInput.sourceEmbedding selection tagged) using 1
open _root_.P2M60f02c0e renaming h70 → _p2mH70
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h71 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (slot : Sigma (_root_.CurrentAFT.PairedRootPlacement.groupRootSlots selection tagged)) (hslot : slot ∉ Set.range (_root_.CurrentAFT.PairedRootInput.sourceEmbedding selection tagged))
    (roots : Sigma (_root_.CurrentAFT.PairedRootPlacement.groupRootSlots selection tagged) → _root_.CurrentAFT.CycleRootExpansion.Root security)
    (root : _root_.CurrentAFT.CycleRootExpansion.Root security) :
    _root_.CurrentAFT.PairedRootCentering.rootDensity selection tagged layout (Function.update roots slot root) = _root_.CurrentAFT.PairedRootCentering.rootDensity selection tagged layout roots := by
  unfold _root_.CurrentAFT.PairedRootCentering.rootDensity
  rw [Function.update_comp_eq_of_forall_ne roots root]
  intro index hequal
  exact hslot ⟨index, hequal⟩
open _root_.P2M60f02c0e renaming h71 → _p2mH71
end
open _root_.P2M60f02c0e renaming h70 → _p2mH70
open _root_.P2M60f02c0e renaming h71 → _p2mH71
end CurrentAFT.PairedRootCentering
open _root_.P2M60f02c0e renaming h70 → _p2mH70
open _root_.P2M60f02c0e renaming h71 → _p2mH71
end
open _root_.P2M60f02c0e renaming h70 → _p2mH70
open _root_.P2M60f02c0e renaming h71 → _p2mH71
namespace CurrentAFT.GroupedSourceNorm
end CurrentAFT.GroupedSourceNorm
namespace CurrentAFT.GroupedSourceNorm.globalReference
end CurrentAFT.GroupedSourceNorm.globalReference
namespace CurrentAFT.GroupedSourceNorm.groupReference
end CurrentAFT.GroupedSourceNorm.groupReference
namespace CurrentAFT.GroupedSourceNorm.wordEquiv
end CurrentAFT.GroupedSourceNorm.wordEquiv
section
namespace CurrentAFT.GroupedRootUpdates
open AFT GroupedSourceNorm
open scoped Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.GroupedRootUpdates.classicalSigmaDecidableEq
variable {Group Root : Type*} [DecidableEq Group] (Slots Control : Group → Type*)
  [∀ group, DecidableEq (Slots group)]
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h52 (word : (group : Group) → (Slots group → Root) × Control group)
    (group : Group) (slot : Slots group) (value : Root) :
    _root_.CurrentAFT.GroupedRootUpdates.roots Slots Control (_root_.CurrentAFT.GroupedRootUpdates.updateRoot Slots Control word group slot value) =
      Function.update (_root_.CurrentAFT.GroupedRootUpdates.roots Slots Control word) ⟨group, slot⟩ value := by
  funext point
  rcases point with ⟨other, point⟩
  by_cases hequal : other = group
  · subst other
    by_cases hslot : point = slot
    · subst point
      simp [_root_.CurrentAFT.GroupedRootUpdates.roots, _root_.CurrentAFT.GroupedRootUpdates.updateRoot]
    · simp [_root_.CurrentAFT.GroupedRootUpdates.roots, _root_.CurrentAFT.GroupedRootUpdates.updateRoot, hslot]
  · simp [_root_.CurrentAFT.GroupedRootUpdates.roots, _root_.CurrentAFT.GroupedRootUpdates.updateRoot, hequal]
open _root_.P2M60f02c0e renaming h52 → _p2mH52
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h51 (word : (group : Group) → (Slots group → Root) × Control group)
    (group : Group) (slot : Slots group) (value : Root) :
    _root_.CurrentAFT.GroupedRootUpdates.controls Slots Control (_root_.CurrentAFT.GroupedRootUpdates.updateRoot Slots Control word group slot value) = _root_.CurrentAFT.GroupedRootUpdates.controls Slots Control word := by
  funext other
  by_cases hequal : other = group
  · subst other
    simp [_root_.CurrentAFT.GroupedRootUpdates.controls, _root_.CurrentAFT.GroupedRootUpdates.updateRoot]
  · simp [_root_.CurrentAFT.GroupedRootUpdates.controls, _root_.CurrentAFT.GroupedRootUpdates.updateRoot, hequal]
open _root_.P2M60f02c0e renaming h51 → _p2mH51
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h53 (word : (group : Group) → (Slots group → Root) × Control group)
    (group : Group) (sample : (Slots group → Root) × Control group) (slot : Slots group) (value : Root) :
    _root_.CurrentAFT.GroupedRootUpdates.updateRoot Slots Control (Function.update word group sample) group slot value =
      Function.update word group (Function.update sample.1 slot value, sample.2) := by
  simp only [_root_.CurrentAFT.GroupedRootUpdates.updateRoot, Function.update_self, Function.update_idem]
open _root_.P2M60f02c0e renaming h53 → _p2mH53
end
open _root_.P2M60f02c0e renaming h51 → _p2mH51
open _root_.P2M60f02c0e renaming h52 → _p2mH52
open _root_.P2M60f02c0e renaming h53 → _p2mH53
end CurrentAFT.GroupedRootUpdates
open _root_.P2M60f02c0e renaming h51 → _p2mH51
open _root_.P2M60f02c0e renaming h52 → _p2mH52
open _root_.P2M60f02c0e renaming h53 → _p2mH53
end
open _root_.P2M60f02c0e renaming h51 → _p2mH51
open _root_.P2M60f02c0e renaming h52 → _p2mH52
open _root_.P2M60f02c0e renaming h53 → _p2mH53
namespace AFT.DependentTensorChannel
end AFT.DependentTensorChannel
namespace AFT.DependentTensorChannel.apply
end AFT.DependentTensorChannel.apply
namespace AFT.DependentTensorChannel.applyFin
end AFT.DependentTensorChannel.applyFin
namespace AFT.DependentTensorChannel.applyFin.match_1
end AFT.DependentTensorChannel.applyFin.match_1
section
namespace CurrentAFT.DependentTensorComposition
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {Index : Type*} [Fintype Index] [DecidableEq Index]
  {Input Middle Output : Index → Type*}
  [∀ index, Fintype (Input index)] [∀ index, Fintype (Middle index)] [∀ index, Fintype (Output index)]
set_option maxRecDepth 8192
omit [∀ index, Fintype (Output index)] in
theorem _root_.P2M60f02c0e.h34
    (first : ∀ index, (Input index → ℝ) →ₗ[ℝ] (Middle index → ℝ))
    (second : ∀ index, (Middle index → ℝ) →ₗ[ℝ] (Output index → ℝ))
    (input : ((index : Index) → Input index) → ℝ) :
    _root_.AFT.DependentTensorChannel.apply (fun index => (second index).comp (first index)) input =
      _root_.AFT.DependentTensorChannel.apply second (_root_.AFT.DependentTensorChannel.apply first input) := by
  funext output
  unfold _root_.AFT.DependentTensorChannel.apply
  simp only [LinearMap.comp_apply]
  have hcolumn (index : Index) (source : Input index) :
      second index (first index (Pi.single source 1)) (output index) =
        ∑ middle, first index (Pi.single source 1) middle *
          second index (Pi.single middle 1) (output index) :=
    _root_.AFT.TensorChannel.channel_sum_single (second index) _ _
  simp_rw [hcolumn]
  simp_rw [Fintype.prod_sum]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro middle _
  apply Finset.sum_congr rfl
  intro source _
  rw [Finset.prod_mul_distrib]
  ring
open _root_.P2M60f02c0e renaming h34 → _p2mH34
end
open _root_.P2M60f02c0e renaming h34 → _p2mH34
end CurrentAFT.DependentTensorComposition
open _root_.P2M60f02c0e renaming h34 → _p2mH34
end
open _root_.P2M60f02c0e renaming h34 → _p2mH34
namespace CurrentAFT.DependentTensorComposition
end CurrentAFT.DependentTensorComposition
section
namespace CurrentAFT.DependentTensorFixedInput
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h35 (count : ℕ) {Input : Fin count → Type*}
    (projector : ∀ index, (Input index → ℝ) →ₗ[ℝ] (Input index → ℝ))
    (kernel : ((index : Fin count) → Input index) → ℝ)
    (hfixed : ∀ index word, projector index
      (fun value => kernel (Function.update word index value)) =
        fun value => kernel (Function.update word index value)) :
    _root_.AFT.DependentTensorChannel.applyFin count projector kernel = kernel := by
  induction count with
  | zero =>
      funext word
      change kernel (fun index => Fin.elim0 index) = kernel word
      congr 1
      funext index
      exact Fin.elim0 index
  | succ count ih =>
      have htail (first : Input 0) :
          ∀ index word, projector index.succ
            (fun value => kernel (Fin.cons first (Function.update word index value))) =
              fun value => kernel (Fin.cons first (Function.update word index value)) := by
        intro index word
        simpa only [Fin.cons_update] using hfixed index.succ (Fin.cons first word)
      have ht (first : Input 0) :
          _root_.AFT.DependentTensorChannel.applyFin count (fun index => projector index.succ)
            (fun rest => kernel (Fin.cons first rest)) =
              fun rest => kernel (Fin.cons first rest) :=
        ih (fun index => projector index.succ) (fun rest => kernel (Fin.cons first rest))
          (htail first)
      funext output
      change projector 0 (fun first =>
        _root_.AFT.DependentTensorChannel.applyFin count (fun index => projector index.succ)
          (fun rest => kernel (Fin.cons first rest)) (fun index => output index.succ))
            (output 0) = kernel output
      simp_rw [ht]
      have hcons : Fin.cons (output 0) (fun index => output index.succ) = output := by
        funext index
        refine Fin.cases ?_ (fun index => ?_) index <;> rfl
      have hh := congrFun (hfixed 0
        (Fin.cons (output 0) (fun index => output index.succ))) (output 0)
      simp only [Fin.update_cons_zero] at hh
      rw [hcons] at hh
      exact hh
open _root_.P2M60f02c0e renaming h35 → _p2mH35
variable {Index : Type*} [Fintype Index] [DecidableEq Index]
  {Input : Index → Type*} [∀ index, Fintype (Input index)]
set_option maxRecDepth 8192
omit [Fintype Index] [∀ index, Fintype (Input index)] in
private theorem _root_.P2M60f02c0e.h261 {Index' : Type*} [DecidableEq Index']
    (equiv : Index' ≃ Index) (word : ∀ index, Input (equiv index))
    (index : Index') (value : Input (equiv index)) :
    Equiv.piCongrLeft Input equiv (Function.update word index value) =
      Function.update (Equiv.piCongrLeft Input equiv word) (equiv index) value := by
  simpa only [Equiv.piCongrLeft, Equiv.symm_symm] using
    Function.piCongrLeft'_symm_update Input equiv.symm word index value
open _root_.P2M60f02c0e renaming h261 → _p2mH261
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h36
    (projector : ∀ index, (Input index → ℝ) →ₗ[ℝ] (Input index → ℝ))
    (kernel : ((index : Index) → Input index) → ℝ)
    (hfixed : ∀ index word, projector index
      (fun value => kernel (Function.update word index value)) =
        fun value => kernel (Function.update word index value)) :
    _root_.AFT.DependentTensorChannel.apply projector kernel = kernel := by
  let equiv : Fin (Fintype.card Index) ≃ Index := (Fintype.equivFin Index).symm
  have hfixed' (index : Fin (Fintype.card Index)) (word : ∀ index, Input (equiv index)) :
      projector (equiv index)
        (fun value => kernel (Equiv.piCongrLeft Input equiv (Function.update word index value))) =
          fun value => kernel (Equiv.piCongrLeft Input equiv (Function.update word index value)) := by
    simpa only [_p2mH261] using
      hfixed (equiv index) (Equiv.piCongrLeft Input equiv word)
  have hh := _p2mH35 (Fintype.card Index) (fun index => projector (equiv index))
    (fun word => kernel (Equiv.piCongrLeft Input equiv word)) hfixed'
  funext output
  have heq := congrFun hh ((Equiv.piCongrLeft Input equiv).symm output)
  rw [_root_.AFT.DependentTensorChannel.applyFin_formula] at heq
  have hreindex :
      (∑ point : (index : Fin (Fintype.card Index)) → Input (equiv index),
        kernel (Equiv.piCongrLeft Input equiv point) *
          ∏ index, projector (equiv index) (Pi.single (point index) 1)
            (((Equiv.piCongrLeft Input equiv).symm output) index)) =
        _root_.AFT.DependentTensorChannel.apply projector kernel output := by
    unfold _root_.AFT.DependentTensorChannel.apply
    rw [← (Equiv.piCongrLeft Input equiv).sum_comp]
    apply Finset.sum_congr rfl
    intro point _
    congr 1
    rw [← equiv.prod_comp]
    simp only [Equiv.piCongrLeft_apply_apply, Equiv.piCongrLeft_symm_apply]
  rw [hreindex] at heq
  simpa only [Equiv.apply_symm_apply] using heq
open _root_.P2M60f02c0e renaming h36 → _p2mH36
end
open _root_.P2M60f02c0e renaming h35 → _p2mH35
open _root_.P2M60f02c0e renaming h36 → _p2mH36
open _root_.P2M60f02c0e renaming h261 → _p2mH261
end CurrentAFT.DependentTensorFixedInput
open _root_.P2M60f02c0e renaming h35 → _p2mH35
open _root_.P2M60f02c0e renaming h36 → _p2mH36
open _root_.P2M60f02c0e renaming h261 → _p2mH261
end
open _root_.P2M60f02c0e renaming h35 → _p2mH35
open _root_.P2M60f02c0e renaming h36 → _p2mH36
namespace CurrentAFT.DependentTensorFixedInput
end CurrentAFT.DependentTensorFixedInput
namespace CurrentAFT.GroupedRootUpdates
end CurrentAFT.GroupedRootUpdates
namespace CurrentAFT.GroupedRootUpdates.controls
end CurrentAFT.GroupedRootUpdates.controls
namespace CurrentAFT.GroupedRootUpdates.roots
end CurrentAFT.GroupedRootUpdates.roots
namespace CurrentAFT.GroupedRootUpdates.updateRoot
end CurrentAFT.GroupedRootUpdates.updateRoot
namespace CurrentAFT.PairedRootCentering
end CurrentAFT.PairedRootCentering
namespace CurrentAFT.RootCoordinateProjection
end CurrentAFT.RootCoordinateProjection
namespace CurrentAFT.RootCoordinateProjection.insert
end CurrentAFT.RootCoordinateProjection.insert
namespace CurrentAFT.RootCoordinateProjection.sequence
end CurrentAFT.RootCoordinateProjection.sequence
section
namespace CurrentAFT.PairedRootProjection
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  PairedRootCentering ControlCoordinates GroupedRootUpdates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.PairedRootProjection.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.PairedRootProjection.classicalSumDecidableEq
attribute [local instance] _root_.CurrentAFT.PairedRootProjection.classicalSigmaDecidableEq
attribute [local instance] _root_.CurrentAFT.PairedRootProjection.slotDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h75 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (slot : Sigma (_root_.CurrentAFT.PairedRootPlacement.groupRootSlots selection tagged)) :
    slot ∈ Set.range (_root_.CurrentAFT.PairedRootInput.sourceEmbedding selection tagged) ↔ _root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged slot ∈ tagged := by
  constructor
  · rintro ⟨index, rfl⟩
    change _root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged (_root_.CurrentAFT.PairedRootPlacement.tagEmbedding selection tagged (tagged.equivFin.symm index)) ∈ tagged
    rw [_root_.CurrentAFT.PairedRootPlacement.tag_image]
    exact (tagged.equivFin.symm index).property
  · intro hslot
    refine ⟨tagged.equivFin ⟨_root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged slot, hslot⟩, ?_⟩
    apply (_root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged).injective
    simp only [_root_.CurrentAFT.PairedRootInput.sourceEmbedding, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
      Equiv.symm_apply_apply, _root_.CurrentAFT.PairedRootPlacement.tag_image]
open _root_.P2M60f02c0e renaming h75 → _p2mH75
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h72 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s)
    (word : _root_.CurrentAFT.PairedRootInput.GroupInput selection tagged) :
    _root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel word =
      _root_.CurrentAFT.PairedRootCentering.rootDensity selection tagged layout (_root_.CurrentAFT.GroupedRootUpdates.roots (_root_.CurrentAFT.PairedRootPlacement.groupRootSlots selection tagged) (_root_.CurrentAFT.PairedRootInput.ControlInput selection tagged) word) *
        _root_.CurrentAFT.PairedRootInput.controlKernel selection tagged kernel (_root_.CurrentAFT.GroupedRootUpdates.controls (_root_.CurrentAFT.PairedRootPlacement.groupRootSlots selection tagged) (_root_.CurrentAFT.PairedRootInput.ControlInput selection tagged) word) := rfl
open _root_.P2M60f02c0e renaming h72 → _p2mH72
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h76 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s)
    (word : _root_.CurrentAFT.PairedRootInput.GroupInput selection tagged) (group : _root_.CurrentAFT.PairedRootPlacement.ActiveGroup selection tagged)
    (slot : _root_.CurrentAFT.PairedRootPlacement.groupRootSlots selection tagged group)
    (htag : _root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged ⟨group, slot⟩ ∈ tagged) :
    (_root_.CurrentAFT.CycleRootExpansion.rootReference security).expectation (fun value =>
      _root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel
        (_root_.CurrentAFT.GroupedRootUpdates.updateRoot (_root_.CurrentAFT.PairedRootPlacement.groupRootSlots selection tagged) (_root_.CurrentAFT.PairedRootInput.ControlInput selection tagged) word group slot value)) = 0 := by
  obtain ⟨index, hindex⟩ := (_p2mH75 selection tagged ⟨group, slot⟩).mpr htag
  simp_rw [_p2mH72, _p2mH52, _p2mH51]
  rw [← hindex]
  unfold _root_.AFT.FiniteDist.expectation
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, _p2mH70 selection tagged layout index, zero_mul]
open _root_.P2M60f02c0e renaming h76 → _p2mH76
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h77 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s)
    (word : _root_.CurrentAFT.PairedRootInput.GroupInput selection tagged) (group : _root_.CurrentAFT.PairedRootPlacement.ActiveGroup selection tagged)
    (slot : _root_.CurrentAFT.PairedRootPlacement.groupRootSlots selection tagged group)
    (htag : _root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged ⟨group, slot⟩ ∉ tagged) (value : _root_.CurrentAFT.CycleRootExpansion.Root security) :
    _root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel
      (_root_.CurrentAFT.GroupedRootUpdates.updateRoot (_root_.CurrentAFT.PairedRootPlacement.groupRootSlots selection tagged) (_root_.CurrentAFT.PairedRootInput.ControlInput selection tagged) word group slot value) =
        _root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel word := by
  rw [_p2mH72, _p2mH52, _p2mH51, _p2mH72]
  rw [_p2mH71 selection tagged layout ⟨group, slot⟩
    (fun h => htag ((_p2mH75 selection tagged ⟨group, slot⟩).mp h))]
open _root_.P2M60f02c0e renaming h77 → _p2mH77
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h74 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s)
    (word : _root_.CurrentAFT.PairedRootInput.GroupInput selection tagged) (group : _root_.CurrentAFT.PairedRootPlacement.ActiveGroup selection tagged) :
    _root_.CurrentAFT.PairedRootProjection.projector selection tagged group (fun sample => _root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel (Function.update word group sample)) =
      fun sample => _root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel (Function.update word group sample) := by
  apply _p2mH208
  intro item hitem
  obtain ⟨slot, _, rfl⟩ := List.mem_map.mp hitem
  by_cases htag : _root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged ⟨group, slot⟩ ∈ tagged
  · simp only [htag, decide_true, _root_.CurrentAFT.RootCoordinateProjection.coordinate, if_true]
    apply _p2mH207
    intro sample
    simp_rw [← _p2mH53]
    exact _p2mH76 selection tagged layout kernel (Function.update word group sample) group slot htag
  · simp only [htag, decide_false, _root_.CurrentAFT.RootCoordinateProjection.coordinate, Bool.false_eq_true, if_false]
    apply _p2mH206
    intro sample value
    rw [← _p2mH53]
    exact _p2mH77 selection tagged layout kernel (Function.update word group sample) group slot htag value
open _root_.P2M60f02c0e renaming h74 → _p2mH74
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h73 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.AFT.DependentTensorChannel.apply (_root_.CurrentAFT.PairedRootProjection.projector selection tagged) (_root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel) =
      _root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel :=
  _p2mH36 _ _ (fun group word =>
    _p2mH74 selection tagged layout kernel word group)
open _root_.P2M60f02c0e renaming h73 → _p2mH73
end
open _root_.P2M60f02c0e renaming h72 → _p2mH72
open _root_.P2M60f02c0e renaming h73 → _p2mH73
open _root_.P2M60f02c0e renaming h74 → _p2mH74
open _root_.P2M60f02c0e renaming h75 → _p2mH75
open _root_.P2M60f02c0e renaming h76 → _p2mH76
open _root_.P2M60f02c0e renaming h77 → _p2mH77
end CurrentAFT.PairedRootProjection
open _root_.P2M60f02c0e renaming h72 → _p2mH72
open _root_.P2M60f02c0e renaming h73 → _p2mH73
open _root_.P2M60f02c0e renaming h74 → _p2mH74
open _root_.P2M60f02c0e renaming h75 → _p2mH75
open _root_.P2M60f02c0e renaming h76 → _p2mH76
open _root_.P2M60f02c0e renaming h77 → _p2mH77
end
open _root_.P2M60f02c0e renaming h72 → _p2mH72
open _root_.P2M60f02c0e renaming h73 → _p2mH73
open _root_.P2M60f02c0e renaming h74 → _p2mH74
open _root_.P2M60f02c0e renaming h75 → _p2mH75
open _root_.P2M60f02c0e renaming h76 → _p2mH76
open _root_.P2M60f02c0e renaming h77 → _p2mH77
namespace CurrentAFT.GroupedFamilyIdentity
end CurrentAFT.GroupedFamilyIdentity
namespace CurrentAFT.GroupedFamilyIdentity.columnKernel
end CurrentAFT.GroupedFamilyIdentity.columnKernel
namespace CurrentAFT.LeadingEvaluation
end CurrentAFT.LeadingEvaluation
namespace CurrentAFT.LeadingEvaluation.familyHom
end CurrentAFT.LeadingEvaluation.familyHom
section
namespace CurrentAFT.GroupedFamilyComposition
open AFT ControlCoordinates ControlProduct GradedControlAlgebra GroupedFamilyTensor
  GroupedKernelNorm
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.GroupedFamilyComposition.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.GroupedFamilyComposition.classicalSigmaDecidableEq
variable {Primary Body Group : Type*} [Fintype Primary] [Fintype Body] [Fintype Group]
  (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
  {Input Middle : Group → Type*}
  [∀ group, Fintype (Input group)] [∀ group, Fintype (Middle group)]
  (preprocess : ∀ group, (Input group → ℝ) →ₗ[ℝ] (Middle group → ℝ))
  (channels : ∀ group, (Middle group → ℝ) →ₗ[ℝ] KernelFamily primary body order)
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h49 (pattern : Group → _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order)
    (input : ((group : Group) → Input group) → ℝ) :
    _root_.CurrentAFT.GroupedFamilyTensor.patternKernel primary body order (fun group => (channels group).comp (preprocess group)) pattern input =
      _root_.CurrentAFT.GroupedFamilyTensor.patternKernel primary body order channels pattern (_root_.AFT.DependentTensorChannel.apply preprocess input) := by
  apply Subtype.ext
  change _root_.CurrentAFT.GroupedKernelNorm.canonicalize _ _ _ _
    (_root_.AFT.DependentTensorChannel.apply
      (_root_.CurrentAFT.GroupedFamilyTensor.componentChannel primary body order (fun group => (channels group).comp (preprocess group)) pattern) input) =
    _root_.CurrentAFT.GroupedKernelNorm.canonicalize _ _ _ _ (_root_.AFT.DependentTensorChannel.apply
      (_root_.CurrentAFT.GroupedFamilyTensor.componentChannel primary body order channels pattern) (_root_.AFT.DependentTensorChannel.apply preprocess input))
  congr 1
  have hchannel : _root_.CurrentAFT.GroupedFamilyTensor.componentChannel primary body order
      (fun group => (channels group).comp (preprocess group)) pattern =
      fun group => (_root_.CurrentAFT.GroupedFamilyTensor.componentChannel primary body order channels pattern group).comp (preprocess group) := rfl
  rw [hchannel, _p2mH34]
open _root_.P2M60f02c0e renaming h49 → _p2mH49
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h48 (pattern : Group → _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order)
    (input : ((group : Group) → Input group) → ℝ) :
    _root_.CurrentAFT.GroupedFamilyTensor.patternFamily primary body order (fun group => (channels group).comp (preprocess group)) pattern input =
      _root_.CurrentAFT.GroupedFamilyTensor.patternFamily primary body order channels pattern (_root_.AFT.DependentTensorChannel.apply preprocess input) := by
  unfold _root_.CurrentAFT.GroupedFamilyTensor.patternFamily
  split_ifs
  · rw [_p2mH49]
  · rfl
open _root_.P2M60f02c0e renaming h48 → _p2mH48
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h50 (input : ((group : Group) → Input group) → ℝ) :
    _root_.CurrentAFT.GroupedFamilyTensor.response primary body order (fun group => (channels group).comp (preprocess group)) input =
      _root_.CurrentAFT.GroupedFamilyTensor.response primary body order channels (_root_.AFT.DependentTensorChannel.apply preprocess input) := by
  unfold _root_.CurrentAFT.GroupedFamilyTensor.response
  simp_rw [_p2mH48]
open _root_.P2M60f02c0e renaming h50 → _p2mH50
end
open _root_.P2M60f02c0e renaming h48 → _p2mH48
open _root_.P2M60f02c0e renaming h49 → _p2mH49
open _root_.P2M60f02c0e renaming h50 → _p2mH50
end CurrentAFT.GroupedFamilyComposition
open _root_.P2M60f02c0e renaming h48 → _p2mH48
open _root_.P2M60f02c0e renaming h49 → _p2mH49
open _root_.P2M60f02c0e renaming h50 → _p2mH50
end
open _root_.P2M60f02c0e renaming h48 → _p2mH48
open _root_.P2M60f02c0e renaming h49 → _p2mH49
open _root_.P2M60f02c0e renaming h50 → _p2mH50
namespace CurrentAFT.ActualRootGroupedChannel
end CurrentAFT.ActualRootGroupedChannel
namespace CurrentAFT.ActualRootGroupedChannel.channel
end CurrentAFT.ActualRootGroupedChannel.channel
namespace CurrentAFT.GroupedFamilyComposition
end CurrentAFT.GroupedFamilyComposition
section
namespace CurrentAFT.ActualRootResponse
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  GradedControlAlgebra ControlCoordinates LocalCoefficientFamily GradedInverse ControlNorm
open Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.ActualRootResponse.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.ActualRootResponse.classicalSumDecidableEq
attribute [local instance] _root_.CurrentAFT.ActualRootResponse.classicalSigmaDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h18 {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s) (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security))
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.CurrentAFT.ActualRootResponse.response order horder queue selection tagged layout kernel =
      _root_.CurrentAFT.GroupedFamilyTensor.response (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order
        (_root_.CurrentAFT.ActualRootGroupedChannel.channel order horder queue selection tagged) (_root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel) := rfl
open _root_.P2M60f02c0e renaming h18 → _p2mH18
end
open _root_.P2M60f02c0e renaming h18 → _p2mH18
end CurrentAFT.ActualRootResponse
open _root_.P2M60f02c0e renaming h18 → _p2mH18
end
open _root_.P2M60f02c0e renaming h18 → _p2mH18
namespace CurrentAFT.ActualCalibrationIteration
end CurrentAFT.ActualCalibrationIteration
namespace CurrentAFT.ActualCalibrationIteration.iterate
end CurrentAFT.ActualCalibrationIteration.iterate
namespace CurrentAFT.ActualCalibrationIteration.iterate.match_1
end CurrentAFT.ActualCalibrationIteration.iterate.match_1
namespace CurrentAFT.ActualCalibrationIteration.step
end CurrentAFT.ActualCalibrationIteration.step
section
namespace CurrentAFT.ActualCoordinateBounds
open AFT ActualControls ProposalPrimary ControlCoordinates ControlProduct ControlNorm
  GradedControlAlgebra GradedControlNorm BackgroundRates LocalCoefficientFamily
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.ActualCoordinateBounds.coordinateFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h10 {State : Type*} [Fintype State] (reference : _root_.AFT.FiniteDist State)
    (test : State → ℝ) (bound : ℝ) (hbound : 1 ≤ bound)
    (point : State) (hatom : 1 ≤ bound * reference.weight point) :
    |test point| ≤ bound * Real.sqrt (reference.l2Sq test) := by
  have he : 0 ≤ reference.l2Sq test := _root_.AFT.FiniteDist.l2Sq_nonneg _ _
  have hp : reference.weight point * test point ^ 2 ≤ reference.l2Sq test :=
    Finset.single_le_sum (fun value _ => mul_nonneg (reference.nonneg value) (sq_nonneg _))
      (Finset.mem_univ point)
  have hs : test point ^ 2 ≤ bound * reference.l2Sq test := by
    have hfirst := mul_le_mul_of_nonneg_right hatom (sq_nonneg (test point))
    have hsecond := mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ bound)
    nlinarith only [hfirst, hsecond]
  have hbb : bound ≤ bound ^ 2 := by nlinarith
  have hlarge := mul_le_mul_of_nonneg_right hbb he
  have hsqrt := Real.sq_sqrt he
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by linarith) (Real.sqrt_nonneg _))).mp
  rw [sq_abs, mul_pow, hsqrt]
  exact hs.trans hlarge
open _root_.P2M60f02c0e renaming h10 → _p2mH10
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h4 {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body) (bound : ℝ) (hbound : 1 ≤ bound)
    (hp : ∀ color, 1 ≤ bound * primary.weight color) (hb : ∀ color, 1 ≤ bound * body.weight color)
    {r s : ℕ} (kernel : _root_.CurrentAFT.ControlCoordinates.DensityKernel (Primary := Primary) (Body := Body) r s)
    (colors : Fin r → Primary) (centers : Fin s → Body) :
    |kernel colors centers| ≤ bound ^ (r + s) * _root_.CurrentAFT.ControlNorm.blockL2 primary body kernel := by
  let reference := (_root_.AFT.FiniteDist.independent (fun _ : Fin r => primary)).prod
    (_root_.AFT.FiniteDist.independent (fun _ : Fin s => body))
  have hatom : 1 ≤ bound ^ (r + s) * reference.weight (colors, centers) := by
    have hfirst : (1 : ℝ) ≤ ∏ index : Fin r, bound * primary.weight (colors index) :=
      Finset.one_le_prod (fun index _ => hp (colors index))
    have hsecond : (1 : ℝ) ≤ ∏ index : Fin s, bound * body.weight (centers index) :=
      Finset.one_le_prod (fun index _ => hb (centers index))
    have hprod := one_le_mul_of_one_le_of_one_le hfirst hsecond
    simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod
    change 1 ≤ bound ^ (r + s) * ((∏ index, primary.weight (colors index)) *
      ∏ index, body.weight (centers index))
    rw [pow_add]
    nlinarith only [hprod]
  exact _p2mH10 reference (fun pair => kernel pair.1 pair.2) _
    (one_le_pow₀ hbound) (colors, centers) hatom
open _root_.P2M60f02c0e renaming h4 → _p2mH4
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h5 (security r s : ℕ)
    (kernel : _root_.CurrentAFT.ControlCoordinates.DensityKernel (Primary := _root_.CurrentAFT.ActualControls.Palette security) (Body := _root_.CurrentAFT.ActualControls.SafePalette security) r s)
    (colors : Fin r → _root_.CurrentAFT.ActualControls.Palette security) (centers : Fin s → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |kernel colors centers| ≤ (2 * (_root_.CurrentAFT.Parameters.modulus security : ℝ)) ^ (r + s) *
      _root_.CurrentAFT.ControlNorm.blockL2 (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) kernel := by
  have hq := _root_.CurrentAFT.FirstResponse.modulus_pos security
  have hq1 : (1 : ℝ) ≤ _root_.CurrentAFT.Parameters.modulus security := by exact_mod_cast (_root_.CurrentAFT.Parameters.modulus_spec security).2.one_le
  apply _p2mH4 _ _ _ (by linarith)
  · intro color
    have h := _root_.CurrentAFT.ProposalPrimary.primaryProfile_atom_lower security color
    have hm := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2 * (Parameters.modulus security : ℝ))
    simpa only [_root_.CurrentAFT.ProposalPrimary.primaryLaw, mul_one_div_cancel (by positivity : (2 * (Parameters.modulus security : ℝ)) ≠ 0)] using hm
  · intro color
    have hm := mul_le_mul_of_nonneg_left (_root_.CurrentAFT.ActualControls.bodyReference_lower security color)
      (by positivity : 0 ≤ 2 * (Parameters.modulus security : ℝ))
    simpa only [mul_one_div_cancel (by positivity : (2 * (Parameters.modulus security : ℝ)) ≠ 0)] using hm
open _root_.P2M60f02c0e renaming h5 → _p2mH5
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h7 (security : ℕ) : (1 : ℝ) ≤ _root_.CurrentAFT.Parameters.dimension security := by
  have h := (_root_.CurrentAFT.Parameters.dimension_bounds security).1
  have hp := pow_pos (_root_.CurrentAFT.Parameters.base_pos security) 160
  exact_mod_cast (show 1 ≤ _root_.CurrentAFT.Parameters.dimension security by omega)
open _root_.P2M60f02c0e renaming h7 → _p2mH7
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h8 (security : ℕ) :
    1 ≤ (_root_.CurrentAFT.Parameters.dimension security : ℝ) * _root_.CurrentAFT.BackgroundRates.primaryFactor security := by
  have hd := _p2mH7 security
  have hl : (_root_.CurrentAFT.Parameters.legCount security : ℝ) ≤ _root_.CurrentAFT.Parameters.dimension security := by
    exact_mod_cast (show _root_.CurrentAFT.Parameters.legCount security ≤ _root_.CurrentAFT.Parameters.dimension security by
      unfold _root_.CurrentAFT.Parameters.dimension; omega)
  have hlpos : (0 : ℝ) < _root_.CurrentAFT.Parameters.legCount security := by
    have h : 0 < _root_.CurrentAFT.Parameters.legCount security := by
      unfold _root_.CurrentAFT.Parameters.legCount _root_.CurrentAFT.Parameters.scale
      exact pow_pos (pow_pos (_root_.CurrentAFT.Parameters.base_pos security) _) _
    exact_mod_cast h
  have hsqrt : Real.sqrt (_root_.CurrentAFT.Parameters.legCount security : ℝ) ≤ _root_.CurrentAFT.Parameters.dimension security := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · linarith
    · nlinarith
  unfold _root_.CurrentAFT.BackgroundRates.primaryFactor
  rw [← div_eq_mul_inv, le_div_iff₀ (Real.sqrt_pos.mpr hlpos), one_mul]
  exact hsqrt
open _root_.P2M60f02c0e renaming h8 → _p2mH8
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h6 (security : ℕ) :
    1 ≤ (_root_.CurrentAFT.Parameters.dimension security : ℝ) * _root_.CurrentAFT.BackgroundRates.bodyFactor security := by
  have hd := _p2mH7 security
  have hp : (0 : ℝ) < _root_.CurrentAFT.BackgroundRates.ordinaryPool security := by exact_mod_cast _root_.CurrentAFT.BackgroundRates.ordinaryPool_pos security
  have hpool : (_root_.CurrentAFT.BackgroundRates.ordinaryPool security : ℝ) ≤ _root_.CurrentAFT.Parameters.dimension security := by
    exact_mod_cast (show _root_.CurrentAFT.BackgroundRates.ordinaryPool security ≤ _root_.CurrentAFT.Parameters.dimension security by
      unfold _root_.CurrentAFT.BackgroundRates.ordinaryPool _root_.CurrentAFT.Parameters.dimension; omega)
  have hr : (1 : ℝ) ≤ _root_.CurrentAFT.BackgroundRates.radius security := by
    apply Real.one_le_rpow
    · exact_mod_cast (_root_.CurrentAFT.Parameters.base_ge_two security).trans' (by omega)
    · norm_num
  have hsqrt : Real.sqrt (_root_.CurrentAFT.BackgroundRates.ordinaryPool security : ℝ) ≤ _root_.CurrentAFT.Parameters.dimension security := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · linarith
    · nlinarith
  unfold _root_.CurrentAFT.BackgroundRates.bodyFactor
  rw [← mul_assoc, ← div_eq_mul_inv, le_div_iff₀ (Real.sqrt_pos.mpr hp), one_mul]
  exact hsqrt.trans (le_mul_of_one_le_right (by linarith) hr)
open _root_.P2M60f02c0e renaming h6 → _p2mH6
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h9 (security order : ℕ) (family : _root_.CurrentAFT.LocalCoefficientFamily.Family security order)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.ActualControls.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |(family arity).val colors centers| ≤
      (2 * (_root_.CurrentAFT.Parameters.modulus security : ℝ) * _root_.CurrentAFT.Parameters.dimension security)^order *
        _root_.CurrentAFT.LocalRaisingBounds.coefficientNorm security order family := by
  have hd := _p2mH7 security
  have hp := (_root_.CurrentAFT.RaisingPatternBudget.primaryFactor_pos security).le
  have hb := (_root_.CurrentAFT.RaisingPatternBudget.bodyFactor_pos security).le
  have hn := _root_.CurrentAFT.GradedControlNorm.familyNorm_nonneg (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order _ _ hp hb family
  have hweight : 1 ≤ (_root_.CurrentAFT.Parameters.dimension security : ℝ)^(arity.val.1.val + arity.val.2.val) *
      _root_.CurrentAFT.ControlNorm.gradeWeight (_root_.CurrentAFT.BackgroundRates.primaryFactor security) (_root_.CurrentAFT.BackgroundRates.bodyFactor security) arity.val.1.val arity.val.2.val := by
    have h := one_le_mul_of_one_le_of_one_le
      (one_le_pow₀ (_p2mH8 security) (n := arity.val.1.val))
      (one_le_pow₀ (_p2mH6 security) (n := arity.val.2.val))
    simpa only [_root_.CurrentAFT.ControlNorm.gradeWeight, mul_pow, pow_add, mul_mul_mul_comm] using h
  have hsingle : _root_.CurrentAFT.ControlNorm.gradeWeight (_root_.CurrentAFT.BackgroundRates.primaryFactor security) (_root_.CurrentAFT.BackgroundRates.bodyFactor security) arity.val.1.val arity.val.2.val *
      _root_.CurrentAFT.ControlNorm.blockL2 (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) (family arity).val ≤
        _root_.CurrentAFT.LocalRaisingBounds.coefficientNorm security order family := by
    unfold _root_.CurrentAFT.LocalRaisingBounds.coefficientNorm _root_.CurrentAFT.GradedControlNorm.familyNorm
    exact Finset.single_le_sum (fun index _ => mul_nonneg
      (_root_.CurrentAFT.ControlNorm.gradeWeight_nonneg _ _ hp hb index.val.1.val index.val.2.val)
      (_root_.CurrentAFT.ControlNorm.blockL2_nonneg (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) (family index).val))
      (Finset.mem_univ arity)
  have hblock : _root_.CurrentAFT.ControlNorm.blockL2 (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) (family arity).val ≤
      (_root_.CurrentAFT.Parameters.dimension security : ℝ)^(arity.val.1.val + arity.val.2.val) *
        _root_.CurrentAFT.LocalRaisingBounds.coefficientNorm security order family := by
    have hfirst := mul_le_mul_of_nonneg_right hweight (_root_.CurrentAFT.ControlNorm.blockL2_nonneg (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) (family arity).val)
    have hsecond := mul_le_mul_of_nonneg_left hsingle
      (pow_nonneg (by linarith : (0 : ℝ) ≤ Parameters.dimension security) (arity.val.1.val + arity.val.2.val))
    nlinarith only [hfirst, hsecond]
  have hq : (1 : ℝ) ≤ _root_.CurrentAFT.Parameters.modulus security := by exact_mod_cast (_root_.CurrentAFT.Parameters.modulus_spec security).2.one_le
  have hlarge : (1 : ℝ) ≤ 2 * (_root_.CurrentAFT.Parameters.modulus security : ℝ) * _root_.CurrentAFT.Parameters.dimension security := by nlinarith
  calc
    _ ≤ (2 * (_root_.CurrentAFT.Parameters.modulus security : ℝ))^(arity.val.1.val + arity.val.2.val) *
        _root_.CurrentAFT.ControlNorm.blockL2 (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) (family arity).val := _p2mH5 security _ _ _ _ _
    _ ≤ (2 * (_root_.CurrentAFT.Parameters.modulus security : ℝ))^(arity.val.1.val + arity.val.2.val) *
        ((_root_.CurrentAFT.Parameters.dimension security : ℝ)^(arity.val.1.val + arity.val.2.val) *
          _root_.CurrentAFT.LocalRaisingBounds.coefficientNorm security order family) := mul_le_mul_of_nonneg_left hblock (by positivity)
    _ = (2 * (_root_.CurrentAFT.Parameters.modulus security : ℝ) * _root_.CurrentAFT.Parameters.dimension security)^(arity.val.1.val + arity.val.2.val) *
        _root_.CurrentAFT.LocalRaisingBounds.coefficientNorm security order family := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hlarge arity.property) hn
open _root_.P2M60f02c0e renaming h9 → _p2mH9
end
open _root_.P2M60f02c0e renaming h4 → _p2mH4
open _root_.P2M60f02c0e renaming h5 → _p2mH5
open _root_.P2M60f02c0e renaming h6 → _p2mH6
open _root_.P2M60f02c0e renaming h7 → _p2mH7
open _root_.P2M60f02c0e renaming h8 → _p2mH8
open _root_.P2M60f02c0e renaming h9 → _p2mH9
open _root_.P2M60f02c0e renaming h10 → _p2mH10
end CurrentAFT.ActualCoordinateBounds
open _root_.P2M60f02c0e renaming h4 → _p2mH4
open _root_.P2M60f02c0e renaming h5 → _p2mH5
open _root_.P2M60f02c0e renaming h6 → _p2mH6
open _root_.P2M60f02c0e renaming h7 → _p2mH7
open _root_.P2M60f02c0e renaming h8 → _p2mH8
open _root_.P2M60f02c0e renaming h9 → _p2mH9
open _root_.P2M60f02c0e renaming h10 → _p2mH10
end
open _root_.P2M60f02c0e renaming h4 → _p2mH4
open _root_.P2M60f02c0e renaming h5 → _p2mH5
open _root_.P2M60f02c0e renaming h6 → _p2mH6
open _root_.P2M60f02c0e renaming h7 → _p2mH7
open _root_.P2M60f02c0e renaming h8 → _p2mH8
open _root_.P2M60f02c0e renaming h9 → _p2mH9
open _root_.P2M60f02c0e renaming h10 → _p2mH10
namespace CurrentAFT.LocalRaisingLinear
end CurrentAFT.LocalRaisingLinear
namespace CurrentAFT.LocalRaisingLinear.primaryEmbeddingLinear
end CurrentAFT.LocalRaisingLinear.primaryEmbeddingLinear
namespace CurrentAFT.RootOrdinaryGroupedChannel
end CurrentAFT.RootOrdinaryGroupedChannel
namespace CurrentAFT.RootSelectedZeroTag
end CurrentAFT.RootSelectedZeroTag
namespace CurrentAFT.RootUnselectedBlockChannel
end CurrentAFT.RootUnselectedBlockChannel
namespace CurrentAFT.RootUnselectedBlockChannel.channel
end CurrentAFT.RootUnselectedBlockChannel.channel
section
namespace CurrentAFT.RootLocalDenominators
open AFT AFT.RepresentedPolynomial DiffuseProfiles ProposalPrimary ActualControls FirstHistogram
  LocalReferenceEnergy PairedReferenceEnergy FixedPairedFirst IndependentPairedReference
  PositiveFirstCoefficient ActualBlockFock RootTaggedSelected RootReferenceExpectation
  RootBackgroundPolynomial RootIndependentBackground BodyRootAverages BackgroundPolynomialEvaluation
  BackgroundEndpointLaw CycleRootExpansion ControlCoordinates GradedControlAlgebra GradedControlNorm
  LocalCoefficientFamily LocalRaisingBounds NormalizedLocalPolynomial
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.RootLocalDenominators.classicalFinDecidableEq
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw rootReference
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h211 (security : ℕ) (queue : ℤ) :
    _root_.CurrentAFT.RootTaggedLocal.meanLaw security .free queue = _root_.CurrentAFT.BackgroundCertificates.convolvedCenterLaw security := by
  unfold _root_.CurrentAFT.RootTaggedLocal.meanLaw _root_.CurrentAFT.RootTaggedLocal.shiftedLaw _root_.CurrentAFT.UniformBodyProfiles.preRootLaw
  rw [_p2mH210, _p2mH19]
open _root_.P2M60f02c0e renaming h211 → _p2mH211
end
open _root_.P2M60f02c0e renaming h211 → _p2mH211
end CurrentAFT.RootLocalDenominators
open _root_.P2M60f02c0e renaming h211 → _p2mH211
end
open _root_.P2M60f02c0e renaming h211 → _p2mH211
namespace CurrentAFT.ActualRootResponse
end CurrentAFT.ActualRootResponse
namespace CurrentAFT.FinitePolynomialTensor
end CurrentAFT.FinitePolynomialTensor
namespace CurrentAFT.FinitePolynomialTensor.synthesis
end CurrentAFT.FinitePolynomialTensor.synthesis
namespace CurrentAFT.RootSelectedPhysicalColumns
end CurrentAFT.RootSelectedPhysicalColumns
namespace CurrentAFT.RootSelectedPhysicalColumns.ordinaryNumerator
end CurrentAFT.RootSelectedPhysicalColumns.ordinaryNumerator
namespace CurrentAFT.RootSelectedPhysicalLinear
end CurrentAFT.RootSelectedPhysicalLinear
namespace CurrentAFT.RootUnselectedPhysicalLinear
end CurrentAFT.RootUnselectedPhysicalLinear
namespace CurrentAFT.RootUnselectedPhysicalLinear.covariance_center
end CurrentAFT.RootUnselectedPhysicalLinear.covariance_center
namespace CurrentAFT.RootUnselectedPhysicalLinear.positiveAt
end CurrentAFT.RootUnselectedPhysicalLinear.positiveAt
namespace CurrentAFT.RootUnselectedPhysicalLinear.positiveAt.match_1
end CurrentAFT.RootUnselectedPhysicalLinear.positiveAt.match_1
namespace CurrentAFT.RootUnselectedPhysicalLinear.rawRoot
end CurrentAFT.RootUnselectedPhysicalLinear.rawRoot
namespace CurrentAFT.RootUnselectedPhysicalLinear.singletonMass
end CurrentAFT.RootUnselectedPhysicalLinear.singletonMass
namespace CurrentAFT.RootUnselectedPhysicalLinear.singletonMass_sum
end CurrentAFT.RootUnselectedPhysicalLinear.singletonMass_sum
section
namespace CurrentAFT.ActualRootPhysicalResponse
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  CycleRootExpansion ControlCoordinates GradedControlAlgebra LocalCoefficientFamily
  RootLocalDenominators FinitePolynomialTensor
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.ActualRootPhysicalResponse.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.ActualRootPhysicalResponse.classicalSumDecidableEq
attribute [local instance] _root_.CurrentAFT.ActualRootPhysicalResponse.classicalProdDecidableEq
attribute [local instance] _root_.CurrentAFT.ActualRootPhysicalResponse.classicalSigmaDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
set_option maxRecDepth 8192
private theorem _root_.P2M60f02c0e.h259 : (Finset.univ : Finset (Fin 1)).toList = [0] := by
  apply Finset.toList_eq_singleton_iff.mpr
  ext index
  rw [Fin.eq_zero index]
  simp
open _root_.P2M60f02c0e renaming h259 → _p2mH259
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h13 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (index : Fin r) :
    _root_.CurrentAFT.PairedRootProjection.projector selection tagged (.inl (.inl index)) =
      _root_.CurrentAFT.RootPrimaryGroupedChannel.projector security (_root_.CurrentAFT.ActualRootGroupedChannel.primaryFlags selection tagged index) := rfl
open _root_.P2M60f02c0e renaming h13 → _p2mH13
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h12 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (index : Fin s) :
    _root_.CurrentAFT.PairedRootProjection.projector selection tagged (.inl (.inr index)) =
      _root_.CurrentAFT.RootOrdinaryGroupedChannel.projector security (_root_.CurrentAFT.ActualRootGroupedChannel.ordinaryFlag selection tagged index) := by
  change _root_.CurrentAFT.RootCoordinateProjection.sequence (_root_.CurrentAFT.CycleRootExpansion.rootReference security)
    ((Finset.univ : Finset (Fin 1)).toList.map (fun slot =>
      (slot, decide (_root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged ⟨.inl (.inr index), slot⟩ ∈ tagged)))) = _
  simp only [_p2mH259, List.map_cons, List.map_nil, _root_.CurrentAFT.RootCoordinateProjection.sequence,
    LinearMap.comp_id]
  rfl
open _root_.P2M60f02c0e renaming h12 → _p2mH12
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h11 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (index : _root_.CurrentAFT.PairedRootPlacement.HitKept selection tagged) :
    _root_.CurrentAFT.PairedRootProjection.projector selection tagged (.inr index) =
      _root_.CurrentAFT.RootCoordinateProjection.center (_root_.CurrentAFT.CycleRootExpansion.rootReference security) (0 : Fin 1) := by
  change _root_.CurrentAFT.RootCoordinateProjection.sequence (_root_.CurrentAFT.CycleRootExpansion.rootReference security)
    ((Finset.univ : Finset (Fin 1)).toList.map (fun slot =>
      (slot, decide (_root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged ⟨.inr index, slot⟩ ∈ tagged)))) = _
  simp only [_p2mH259, List.map_cons, List.map_nil, _root_.CurrentAFT.RootCoordinateProjection.sequence,
    LinearMap.comp_id]
  have hroot : _root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged ⟨.inr index, (0 : Fin 1)⟩ = index.val.val := rfl
  rw [hroot]
  simp only [index.property, decide_true, _root_.CurrentAFT.RootCoordinateProjection.coordinate, if_true]
open _root_.P2M60f02c0e renaming h11 → _p2mH11
end
open _root_.P2M60f02c0e renaming h11 → _p2mH11
open _root_.P2M60f02c0e renaming h12 → _p2mH12
open _root_.P2M60f02c0e renaming h13 → _p2mH13
open _root_.P2M60f02c0e renaming h259 → _p2mH259
end CurrentAFT.ActualRootPhysicalResponse
open _root_.P2M60f02c0e renaming h11 → _p2mH11
open _root_.P2M60f02c0e renaming h12 → _p2mH12
open _root_.P2M60f02c0e renaming h13 → _p2mH13
open _root_.P2M60f02c0e renaming h259 → _p2mH259
end
open _root_.P2M60f02c0e renaming h11 → _p2mH11
open _root_.P2M60f02c0e renaming h12 → _p2mH12
open _root_.P2M60f02c0e renaming h13 → _p2mH13
namespace CurrentAFT.ActualRootPhysicalResponse
end CurrentAFT.ActualRootPhysicalResponse
namespace CurrentAFT.ActualRootPhysicalResponse.localDenominator
end CurrentAFT.ActualRootPhysicalResponse.localDenominator
namespace CurrentAFT.ActualRootPhysicalResponse.localDenominator.match_1
end CurrentAFT.ActualRootPhysicalResponse.localDenominator.match_1
namespace CurrentAFT.ActualRootPhysicalResponse.projectedPhysical
end CurrentAFT.ActualRootPhysicalResponse.projectedPhysical
namespace CurrentAFT.ActualRootPhysicalResponse.rawPhysical
end CurrentAFT.ActualRootPhysicalResponse.rawPhysical
namespace CurrentAFT.RootOrdinaryGroupedChannel.channel
end CurrentAFT.RootOrdinaryGroupedChannel.channel
namespace CurrentAFT.RootSelectedControlCenter
end CurrentAFT.RootSelectedControlCenter
namespace CurrentAFT.RootSelectedControlCenter.projector
end CurrentAFT.RootSelectedControlCenter.projector
namespace CurrentAFT.RootSelectedControlCenter.projector.match_1
end CurrentAFT.RootSelectedControlCenter.projector.match_1
namespace CurrentAFT.RootUnselectedGrouped
end CurrentAFT.RootUnselectedGrouped
namespace CurrentAFT.RootUnselectedGrouped.channel
end CurrentAFT.RootUnselectedGrouped.channel
section
namespace CurrentAFT.ActualRootProjectionData
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  CycleRootExpansion ControlCoordinates GradedControlAlgebra LocalCoefficientFamily
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.ActualRootProjectionData.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.ActualRootProjectionData.classicalSumDecidableEq
attribute [local instance] _root_.CurrentAFT.ActualRootProjectionData.classicalProdDecidableEq
attribute [local instance] _root_.CurrentAFT.ActualRootProjectionData.classicalSigmaDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h17 (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (block : _root_.CurrentAFT.ActualBlockFock.BlockIndex security) (constant : ℝ) :
    _root_.CurrentAFT.RootUnselectedBlockChannel.channel security order horder queue block (fun _ => constant) = 0 := by
  have hconstant : (fun _ : _root_.CurrentAFT.CycleRootExpansion.Root security => constant) = constant • (fun _ => (1 : ℝ)) := by
    funext root
    simp only [Pi.smul_apply, smul_eq_mul, mul_one]
  rw [hconstant, map_smul]
  suffices h : _root_.CurrentAFT.RootUnselectedBlockChannel.channel security order horder queue block (fun _ => 1) = 0 by
    rw [h, smul_zero]
  have hsingle (role : _root_.CurrentAFT.UniformBodyProfiles.BodyRole) (shift : ℤ) :
      _root_.CurrentAFT.RootUnselectedChannels.singletonChannel security order horder role shift (fun _ => 1) = 0 := by
    change _root_.CurrentAFT.RootTaggedFamilies.rootFamilyLinear security order horder role shift (fun _ => 1) * _ = 0
    rw [_p2mH247, zero_mul]
  rcases block with leg | single
  · change (_root_.CurrentAFT.RootTaggedFamilies.rootFamilyLinear security order horder .attachment 0 (fun _ => 1) +
      _root_.CurrentAFT.RootLegCoefficientLinear.rootHigherLinear security order (fun _ => 1)) * _ = 0
    rw [_p2mH247]
    change (0 + _root_.CurrentAFT.RootLegCoefficientLinear.higherFamilyLinear security order
      (_root_.CurrentAFT.RootTaggedLegHigher.massLinear security (fun _ => 1))) * _ = 0
    rw [_p2mH248, map_zero, add_zero, zero_mul]
  · rcases single with center | point
    · exact hsingle .free 0
    · exact hsingle .queue queue
open _root_.P2M60f02c0e renaming h17 → _p2mH17
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h16 (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (block : _root_.CurrentAFT.ActualBlockFock.BlockIndex security) (score : _root_.CurrentAFT.RootUnselectedGrouped.Input security → ℝ) :
    _root_.CurrentAFT.RootUnselectedGrouped.channel security order horder queue block
      (_root_.CurrentAFT.RootCoordinateProjection.center (_root_.CurrentAFT.CycleRootExpansion.rootReference security) (0 : Fin 1) score) =
        _root_.CurrentAFT.RootUnselectedGrouped.channel security order horder queue block score := by
  have haverage : _root_.CurrentAFT.RootUnselectedGrouped.extractLinear security
      (_root_.CurrentAFT.RootCoordinateProjection.average (_root_.CurrentAFT.CycleRootExpansion.rootReference security) (0 : Fin 1) score) =
      fun _ => (_root_.CurrentAFT.CycleRootExpansion.rootReference security).expectation (_root_.CurrentAFT.RootUnselectedGrouped.extractLinear security score) := by
    funext root
    change (_root_.CurrentAFT.CycleRootExpansion.rootReference security).expectation (fun other =>
      score (Function.update (fun _ : Fin 1 => root) 0 other, ())) = _
    simp only [Function.update_eq_const_of_subsingleton]
    rfl
  change _root_.CurrentAFT.RootUnselectedBlockChannel.channel security order horder queue block
    (_root_.CurrentAFT.RootUnselectedGrouped.extractLinear security (score - _root_.CurrentAFT.RootCoordinateProjection.average (_root_.CurrentAFT.CycleRootExpansion.rootReference security) (0 : Fin 1) score)) = _
  rw [map_sub, haverage, map_sub, _p2mH17, sub_zero]
  rfl
open _root_.P2M60f02c0e renaming h16 → _p2mH16
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h14 {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s) (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security))
    (group : _root_.CurrentAFT.PairedRootPlacement.ActiveGroup selection tagged) :
    _root_.CurrentAFT.ActualRootGroupedChannel.channel order horder queue selection tagged group =
      (_root_.CurrentAFT.ActualRootProjectionData.unprojectedChannel order horder queue selection tagged group).comp
        (_root_.CurrentAFT.PairedRootProjection.projector selection tagged group) := by
  rcases group with (primary | ordinary) | kept
  · rw [_p2mH13]
    rfl
  · rw [_p2mH12]
    rfl
  · rw [_p2mH11]
    apply LinearMap.ext
    intro score
    exact (_p2mH16 security order horder queue kept.val.val score).symm
open _root_.P2M60f02c0e renaming h14 → _p2mH14
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h15 {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s) (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security))
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.CurrentAFT.ActualRootResponse.response order horder queue selection tagged layout kernel =
      _root_.CurrentAFT.GroupedFamilyTensor.response (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order
        (_root_.CurrentAFT.ActualRootProjectionData.unprojectedChannel order horder queue selection tagged) (_root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel) := by
  rw [_p2mH18]
  have hchannels : _root_.CurrentAFT.ActualRootGroupedChannel.channel order horder queue selection tagged = fun group =>
      (_root_.CurrentAFT.ActualRootProjectionData.unprojectedChannel order horder queue selection tagged group).comp
        (_root_.CurrentAFT.PairedRootProjection.projector selection tagged group) :=
    funext (_p2mH14 order horder queue selection tagged)
  rw [hchannels, _p2mH50, _p2mH73]
open _root_.P2M60f02c0e renaming h15 → _p2mH15
end
open _root_.P2M60f02c0e renaming h14 → _p2mH14
open _root_.P2M60f02c0e renaming h15 → _p2mH15
open _root_.P2M60f02c0e renaming h16 → _p2mH16
open _root_.P2M60f02c0e renaming h17 → _p2mH17
end CurrentAFT.ActualRootProjectionData
open _root_.P2M60f02c0e renaming h14 → _p2mH14
open _root_.P2M60f02c0e renaming h15 → _p2mH15
open _root_.P2M60f02c0e renaming h16 → _p2mH16
open _root_.P2M60f02c0e renaming h17 → _p2mH17
end
open _root_.P2M60f02c0e renaming h14 → _p2mH14
open _root_.P2M60f02c0e renaming h15 → _p2mH15
open _root_.P2M60f02c0e renaming h16 → _p2mH16
open _root_.P2M60f02c0e renaming h17 → _p2mH17
namespace CurrentAFT.CalibrationPointCoordinates
end CurrentAFT.CalibrationPointCoordinates
namespace CurrentAFT.CalibrationPointCoordinates.currentMatrix
end CurrentAFT.CalibrationPointCoordinates.currentMatrix
namespace CurrentAFT.CalibrationPointCoordinates.decode
end CurrentAFT.CalibrationPointCoordinates.decode
namespace CurrentAFT.CalibrationPointCoordinates.extend
end CurrentAFT.CalibrationPointCoordinates.extend
namespace CurrentAFT.CanonicalReconstruction
end CurrentAFT.CanonicalReconstruction
namespace CurrentAFT.CanonicalReconstruction.pointKernel
end CurrentAFT.CanonicalReconstruction.pointKernel
section
namespace CurrentAFT.CalibrationCoordinateError
open AFT ControlCoordinates ControlProduct ControlNorm CanonicalReconstruction
  GradedControlAlgebra GradedControlNorm CalibrationPointCoordinates
  ActualControls ProposalPrimary BackgroundRates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.CalibrationCoordinateError.coordinateFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h21 {State : Type*} [Fintype State]
    (law : _root_.AFT.FiniteDist State) (value : State → ℝ) (bound : ℝ)
    (hbound : ∀ state, |value state| ≤ bound) : |law.expectation value| ≤ bound := by
  unfold _root_.AFT.FiniteDist.expectation
  calc
    _ ≤ ∑ state, |law.weight state * value state| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ state, law.weight state * bound := by
      apply Finset.sum_le_sum
      intro state _
      rw [abs_mul, abs_of_nonneg (law.nonneg state)]
      exact mul_le_mul_of_nonneg_left (hbound state) (law.nonneg state)
    _ = bound := by rw [← Finset.sum_mul, law.sum_one, one_mul]
open _root_.P2M60f02c0e renaming h21 → _p2mH21
variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]
end
open _root_.P2M60f02c0e renaming h21 → _p2mH21
end CurrentAFT.CalibrationCoordinateError
open _root_.P2M60f02c0e renaming h21 → _p2mH21
end
open _root_.P2M60f02c0e renaming h21 → _p2mH21
namespace AFT.RationalNumerics
end AFT.RationalNumerics
namespace AFT.RationalNumerics.linearIteration
end AFT.RationalNumerics.linearIteration
namespace AFT.RationalNumerics.linearIteration.match_1
end AFT.RationalNumerics.linearIteration.match_1
namespace AFT.RationalNumerics.matrixApply
end AFT.RationalNumerics.matrixApply
namespace AFT.RationalNumerics.realLinearIteration
end AFT.RationalNumerics.realLinearIteration
namespace AFT.RationalNumerics.realMatrixOperator
end AFT.RationalNumerics.realMatrixOperator
section
namespace CurrentAFT.CalibrationRectanglePadding
open AFT RationalNumerics
open scoped BigOperators
variable {Small Large : Type*}
section
variable [Fintype Small] [Fintype Large]
variable (encode : Small ↪ Large) (decode : Large → Option Small)
variable (hdecode : ∀ point small, decode point = some small ↔ point = encode small)
include encode hdecode
set_option maxRecDepth 8192
omit [Fintype Small] [Fintype Large] in
theorem _root_.P2M60f02c0e.h22 (point : Small) : decode (encode point) = some point :=
  (hdecode _ _).mpr rfl
open _root_.P2M60f02c0e renaming h22 → _p2mH22
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h23 {Scalar : Type*} [AddCommMonoid Scalar] (table : Small → Scalar) :
    (∑ point, _root_.CurrentAFT.CalibrationRectanglePadding.extend decode table point) = ∑ point, table point := by
  have hsubset : Finset.univ.map encode ⊆ (Finset.univ : Finset Large) := Finset.subset_univ _
  have hsum := Finset.sum_subset hsubset (f := _root_.CurrentAFT.CalibrationRectanglePadding.extend decode table) (by
    intro point _ hnot
    have hn : decode point = none := by
      cases hd : decode point with
      | none => rfl
      | some small =>
        have hp := (hdecode point small).mp hd
        subst point
        exact False.elim (hnot (Finset.mem_map.mpr ⟨small, Finset.mem_univ _, rfl⟩))
    simp only [_root_.CurrentAFT.CalibrationRectanglePadding.extend, hn, Option.elim_none])
  rw [← hsum, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro point _
  simp only [_root_.CurrentAFT.CalibrationRectanglePadding.extend, _p2mH22 encode decode hdecode, Option.elim_some]
open _root_.P2M60f02c0e renaming h23 → _p2mH23
end
open _root_.P2M60f02c0e renaming h22 → _p2mH22
open _root_.P2M60f02c0e renaming h23 → _p2mH23
end CurrentAFT.CalibrationRectanglePadding
open _root_.P2M60f02c0e renaming h22 → _p2mH22
open _root_.P2M60f02c0e renaming h23 → _p2mH23
end
open _root_.P2M60f02c0e renaming h22 → _p2mH22
open _root_.P2M60f02c0e renaming h23 → _p2mH23
namespace CurrentAFT.CalibrationRectanglePadding
end CurrentAFT.CalibrationRectanglePadding
namespace CurrentAFT.CalibrationRectanglePadding.defect
end CurrentAFT.CalibrationRectanglePadding.defect
namespace CurrentAFT.CalibrationRectanglePadding.extend
end CurrentAFT.CalibrationRectanglePadding.extend
namespace CurrentAFT.WeightCoordinates
end CurrentAFT.WeightCoordinates
namespace CurrentAFT.WeightCoordinates.tupleDecode
end CurrentAFT.WeightCoordinates.tupleDecode
namespace CurrentAFT.WeightCoordinates.tupleDecode.match_1
end CurrentAFT.WeightCoordinates.tupleDecode.match_1
section
namespace CurrentAFT.GroupSourcePadding
open scoped BigOperators
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h43 (q : ℕ) (hq : 0 < q) (safe : Fin q → Prop) (kind : _root_.CurrentAFT.GroupSourcePadding.Kind)
    (word : Fin 3 → Fin q) (h : _root_.CurrentAFT.GroupSourcePadding.Valid q safe kind word) :
    _root_.CurrentAFT.GroupSourcePadding.encode q hq safe kind (_root_.CurrentAFT.GroupSourcePadding.recover q safe kind word h) = word := by
  funext slot
  cases kind with
  | primary => fin_cases slot <;> rfl
  | ordinary =>
    fin_cases slot
    · rfl
    · rfl
    · apply Fin.ext; exact h.2.symm
  | kept =>
    fin_cases slot
    · rfl
    · apply Fin.ext; exact h.1.symm
    · apply Fin.ext; exact h.2.symm
open _root_.P2M60f02c0e renaming h43 → _p2mH43
section Grouped
variable {Group : Type*} [Fintype Group] (q : ℕ) (hq : 0 < q) (safe : Fin q → Prop) [DecidablePred safe]
  (kind : Group → Kind)
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h45 (source : _root_.CurrentAFT.GroupSourcePadding.Source q safe kind) :
    _root_.CurrentAFT.GroupSourcePadding.sourceDecode q safe kind (_root_.CurrentAFT.GroupSourcePadding.sourceEncode q hq safe kind source) = some source := by
  unfold _root_.CurrentAFT.GroupSourcePadding.sourceDecode _root_.CurrentAFT.GroupSourcePadding.sourceEncode
  rw [dif_pos (fun group => _root_.CurrentAFT.GroupSourcePadding.encode_valid q hq safe (kind group) (source group))]
  congr 1
  funext group
  exact _root_.CurrentAFT.GroupSourcePadding.recover_encode q hq safe (kind group) (source group)
open _root_.P2M60f02c0e renaming h45 → _p2mH45
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h46 (word : _root_.CurrentAFT.GroupSourcePadding.Word (Group := Group) q) (source : _root_.CurrentAFT.GroupSourcePadding.Source q safe kind) :
    _root_.CurrentAFT.GroupSourcePadding.sourceDecode q safe kind word = some source ↔ word = _root_.CurrentAFT.GroupSourcePadding.sourceEncode q hq safe kind source := by
  constructor
  · intro h
    unfold _root_.CurrentAFT.GroupSourcePadding.sourceDecode at h
    split at h
    · rename_i hv
      have he := Option.some.inj h
      subst source
      funext group
      exact (_p2mH43 q hq safe (kind group) (word group) (hv group)).symm
    · cases h
  · rintro rfl
    exact _p2mH45 q hq safe kind source
open _root_.P2M60f02c0e renaming h46 → _p2mH46
end Grouped
open _root_.P2M60f02c0e renaming h45 → _p2mH45
open _root_.P2M60f02c0e renaming h46 → _p2mH46
section Indexed
variable {Group : Type*} [Fintype Group] [DecidableEq Group] (q : ℕ) (hq : 0 < q) (safe : Fin q → Prop) [DecidablePred safe]
  (kind : Group → Kind) (count : ℕ) (ordering : Fin count ≃ Group)
set_option maxRecDepth 8192
omit [DecidableEq Group] in
theorem _root_.P2M60f02c0e.h44 (index : Fin (q^(count*3))) (source : _root_.CurrentAFT.GroupSourcePadding.Source q safe kind) :
    _root_.CurrentAFT.GroupSourcePadding.indexDecode q hq safe kind count ordering index = some source ↔
      index = _root_.CurrentAFT.GroupSourcePadding.indexEncode q hq safe kind count ordering source := by
  rw [_root_.CurrentAFT.GroupSourcePadding.indexDecode, _p2mH46 q hq safe kind]
  exact (_root_.CurrentAFT.GroupSourcePadding.indexEquiv q hq count ordering).symm_apply_eq
open _root_.P2M60f02c0e renaming h44 → _p2mH44
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h47 {Scalar : Type*} [AddCommMonoid Scalar] (summand : _root_.CurrentAFT.GroupSourcePadding.Source q safe kind → Scalar) :
    (∑ index : Fin (q^(count*3)), (_root_.CurrentAFT.GroupSourcePadding.indexDecode q hq safe kind count ordering index).elim 0 summand) =
      ∑ source, summand source :=
  _p2mH23 (_root_.CurrentAFT.GroupSourcePadding.indexEncode q hq safe kind count ordering)
    (_root_.CurrentAFT.GroupSourcePadding.indexDecode q hq safe kind count ordering) (_p2mH44 q hq safe kind count ordering) summand
open _root_.P2M60f02c0e renaming h47 → _p2mH47
end Indexed
open _root_.P2M60f02c0e renaming h44 → _p2mH44
open _root_.P2M60f02c0e renaming h47 → _p2mH47
end CurrentAFT.GroupSourcePadding
open _root_.P2M60f02c0e renaming h43 → _p2mH43
open _root_.P2M60f02c0e renaming h44 → _p2mH44
open _root_.P2M60f02c0e renaming h45 → _p2mH45
open _root_.P2M60f02c0e renaming h46 → _p2mH46
open _root_.P2M60f02c0e renaming h47 → _p2mH47
end
open _root_.P2M60f02c0e renaming h43 → _p2mH43
open _root_.P2M60f02c0e renaming h44 → _p2mH44
open _root_.P2M60f02c0e renaming h45 → _p2mH45
open _root_.P2M60f02c0e renaming h46 → _p2mH46
open _root_.P2M60f02c0e renaming h47 → _p2mH47
namespace CurrentAFT.CurrentCycleEntryProgram
end CurrentAFT.CurrentCycleEntryProgram
namespace CurrentAFT.CurrentCycleEntryProgram.bodyCount
end CurrentAFT.CurrentCycleEntryProgram.bodyCount
namespace CurrentAFT.CycleRootExpansion.actualComponent
end CurrentAFT.CycleRootExpansion.actualComponent
namespace CurrentAFT.CycleRootExpansion.selectedCoefficient
end CurrentAFT.CycleRootExpansion.selectedCoefficient
namespace CurrentAFT.CycleSelections.centeredRootDensity
end CurrentAFT.CycleSelections.centeredRootDensity
namespace CurrentAFT.ProtectedCycle.cycleLaw
end CurrentAFT.ProtectedCycle.cycleLaw
namespace CurrentAFT.SelectedRootComponent
end CurrentAFT.SelectedRootComponent
section
namespace CurrentAFT.RootSignedMassProgram
open AFT GaussianSource CycleSelections CyclePatternProgram CycleRootExpansion
  CurrentCycleEntryProgram DiffuseProfiles
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base Parameters.bodySize
attribute [local instance] _root_.CurrentAFT.RootSignedMassProgram.modulusNeZero
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h246 (Index Color : Type*) [Fintype Index] [DecidableEq Index] [Fintype Color] [DecidableEq Color]
    (joint : _root_.AFT.FiniteDist (Index → Color)) (reference : Index → _root_.AFT.FiniteDist Color)
    (hsupport : ∀ input, joint.weight input ≠ 0 → ∀ index, 0 < (reference index).weight (input index))
    (output : Index → Color) :
    (∏ index, (reference index).weight (output index)) * _root_.CurrentAFT.CycleSelections.centeredRootDensity joint reference output =
      joint.expectation (fun input => ∏ index,
        ((if input index = output index then (1 : ℝ) else 0) - (reference index).weight (output index))) := by
  unfold _root_.CurrentAFT.CycleSelections.centeredRootDensity _root_.AFT.FiniteDist.expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro input _
  by_cases hzero : joint.weight input = 0
  · simp only [hzero, zero_mul, mul_zero]
  · have hpoint (index : Index) : (reference index).weight (output index) *
        _root_.CurrentAFT.CycleSelections.centeredRootAtom (reference index) (input index) (output index) =
          (if input index = output index then (1 : ℝ) else 0) - (reference index).weight (output index) := by
      by_cases hout : (reference index).weight (output index) = 0
      · have hne : input index ≠ output index := by
          intro hequal
          have hpos := hsupport input hzero index
          rw [hequal, hout] at hpos
          exact (lt_irrefl 0) hpos
        simp only [_root_.CurrentAFT.CycleSelections.centeredRootAtom, hout, hne, if_false, zero_mul, sub_zero]
      · unfold _root_.CurrentAFT.CycleSelections.centeredRootAtom
        by_cases hequal : input index = output index
        · simp only [if_pos hequal]
          field_simp
        · simp only [if_neg hequal]
          field_simp
    calc
      _ = joint.weight input *
          ((∏ index, (reference index).weight (output index)) *
            ∏ index, _root_.CurrentAFT.CycleSelections.centeredRootAtom (reference index) (input index) (output index)) := by ring
      _ = joint.weight input * (∏ index, (reference index).weight (output index) *
          _root_.CurrentAFT.CycleSelections.centeredRootAtom (reference index) (input index) (output index)) := by rw [Finset.prod_mul_distrib]
      _ = _ := by congr 1; exact Finset.prod_congr rfl (fun index _ => hpoint index)
open _root_.P2M60f02c0e renaming h246 → _p2mH246
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h245 (security order : ℕ)
    (labels : _root_.CurrentAFT.CycleSelections.Selection (_root_.CurrentAFT.Parameters.bodySize security) order) (output : Fin order → _root_.CurrentAFT.CycleRootExpansion.Root security) :
    (∏ index, (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight (output index)) * _root_.CurrentAFT.CycleRootExpansion.selectedCoefficient security order labels output =
      ((_root_.CurrentAFT.CycleRootExpansion.rootLaw security).map (fun roots index => roots (labels index))).expectation
        (fun input => ∏ index, ((if input index = output index then (1 : ℝ) else 0) -
          (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight (output index))) := by
  unfold _root_.CurrentAFT.CycleRootExpansion.selectedCoefficient
  apply _p2mH246
  apply _p2mH30
  intro index
  rw [_root_.AFT.FiniteDist.map_map]
  exact _p2mH31 security (labels index)
open _root_.P2M60f02c0e renaming h245 → _p2mH245
end
open _root_.P2M60f02c0e renaming h245 → _p2mH245
open _root_.P2M60f02c0e renaming h246 → _p2mH246
end CurrentAFT.RootSignedMassProgram
open _root_.P2M60f02c0e renaming h245 → _p2mH245
open _root_.P2M60f02c0e renaming h246 → _p2mH246
end
open _root_.P2M60f02c0e renaming h245 → _p2mH245
open _root_.P2M60f02c0e renaming h246 → _p2mH246
namespace CurrentAFT.CycleSelections.centeredRootAtom
end CurrentAFT.CycleSelections.centeredRootAtom
namespace CurrentAFT.RootCoordinateProjection.coordinate
end CurrentAFT.RootCoordinateProjection.coordinate
namespace CurrentAFT.RootCoordinateProjection.sequence.match_1
end CurrentAFT.RootCoordinateProjection.sequence.match_1
namespace CurrentAFT.RootPrimaryGroupedChannel
end CurrentAFT.RootPrimaryGroupedChannel
namespace CurrentAFT.RootPrimaryGroupedChannel.cost
end CurrentAFT.RootPrimaryGroupedChannel.cost
namespace CurrentAFT.RootPrimaryGroupedChannel.minimumDegree
end CurrentAFT.RootPrimaryGroupedChannel.minimumDegree
namespace CurrentAFT.RootPrimaryGroupedChannel.pairEquiv
end CurrentAFT.RootPrimaryGroupedChannel.pairEquiv
namespace CurrentAFT.RootPrimaryGroupedChannel.pairLinear
end CurrentAFT.RootPrimaryGroupedChannel.pairLinear
namespace CurrentAFT.RootPrimaryGroupedChannel.projectedScore
end CurrentAFT.RootPrimaryGroupedChannel.projectedScore
namespace CurrentAFT.RootSignedMassProgram
end CurrentAFT.RootSignedMassProgram
namespace CurrentAFT.RootSignedMassProgram.referenceEntry
end CurrentAFT.RootSignedMassProgram.referenceEntry
namespace CurrentAFT.RootSignedMassProgram.signedTest
end CurrentAFT.RootSignedMassProgram.signedTest
namespace CurrentAFT.RootTaggedSelectedChannel
end CurrentAFT.RootTaggedSelectedChannel
namespace CurrentAFT.RootTaggedSelectedChannel.curryLinear
end CurrentAFT.RootTaggedSelectedChannel.curryLinear
section
namespace CurrentAFT.RootMassColumns
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion
  LocalReferenceEnergy FirstHistogram ControlCoordinates GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw bodyReference rootReference
attribute [local instance] _root_.CurrentAFT.RootMassColumns.classicalFinDecidableEq
section Fiber
variable {Root Control Output : Type*} [Fintype Root]
  [AddCommMonoid Output] [Module ℝ Output]
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h220 (reference : _root_.AFT.FiniteDist Root)
    (channel : Root → (Control → ℝ) →ₗ[ℝ] Output)
    (root : Root) (score : Control → ℝ) :
    (∑ other, reference.weight other • channel other (_root_.CurrentAFT.RootMassColumns.fiber root score other)) =
      reference.weight root • channel root score := by
  classical
  calc
    _ = reference.weight root • channel root (_root_.CurrentAFT.RootMassColumns.fiber root score root) :=
      Finset.sum_eq_single root (fun other _ hne => by
        simp only [_root_.CurrentAFT.RootMassColumns.fiber, if_neg hne, map_zero, smul_zero]) (by simp)
    _ = _ := by simp [_root_.CurrentAFT.RootMassColumns.fiber]
open _root_.P2M60f02c0e renaming h220 → _p2mH220
end Fiber
open _root_.P2M60f02c0e renaming h220 → _p2mH220
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h215 (security : ℕ)
    (score : _root_.CurrentAFT.RootTaggedSelected.RootPair security → _root_.CurrentAFT.ActualControls.Palette security → ℝ) :
    _root_.CurrentAFT.RootTaggedSelected.massLinear security score =
      ∑ roots, (_root_.CurrentAFT.RootTaggedSelected.rootsLaw security).weight roots •
        _root_.CurrentAFT.RootMassColumns.primaryMassAt security roots (score roots) := by
  funext word
  simp only [_root_.CurrentAFT.RootTaggedSelected.massLinear, _root_.CurrentAFT.RootTaggedSelected.sourceLaw, _root_.CurrentAFT.RootMassColumns.primaryMassAt,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, _root_.AFT.FiniteDist.prod_weight, Fintype.sum_prod_type,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro roots _
  apply Finset.sum_congr rfl
  intro scalar _
  simp only [mul_assoc]
open _root_.P2M60f02c0e renaming h215 → _p2mH215
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h216 (security : ℕ) (roots : _root_.CurrentAFT.RootTaggedSelected.RootPair security)
    (score : _root_.CurrentAFT.ActualControls.Palette security → ℝ) :
    _root_.CurrentAFT.RootTaggedSelected.massLinear security (_root_.CurrentAFT.RootMassColumns.fiber roots score) =
      (_root_.CurrentAFT.RootTaggedSelected.rootsLaw security).weight roots • _root_.CurrentAFT.RootMassColumns.primaryMassAt security roots score := by
  rw [_p2mH215]
  exact _p2mH220 _ (_root_.CurrentAFT.RootMassColumns.primaryMassAt security) roots score
open _root_.P2M60f02c0e renaming h216 → _p2mH216
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h217 (security order : ℕ) (roots : _root_.CurrentAFT.RootTaggedSelected.RootPair security)
    (score : _root_.CurrentAFT.ActualControls.Palette security → ℝ) :
    _root_.CurrentAFT.RootTaggedSelectedChannel.responseLinear security order (_root_.CurrentAFT.RootMassColumns.fiber roots score) =
      (_root_.CurrentAFT.RootTaggedSelected.rootsLaw security).weight roots • _root_.CurrentAFT.RootMassColumns.primaryResponseAt security order roots score := by
  change _root_.CurrentAFT.LocalRaisingLinear.completeFamilyLinear security order
    (_root_.CurrentAFT.RootTaggedSelected.massLinear security (_root_.CurrentAFT.RootMassColumns.fiber roots score)) * _ = _
  rw [_p2mH216, map_smul, smul_mul_assoc]
  rfl
open _root_.P2M60f02c0e renaming h217 → _p2mH217
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h218 (security : ℕ) (roots : _root_.CurrentAFT.RootTaggedSelected.RootPair security) :
    (_root_.CurrentAFT.RootTaggedSelected.rootsLaw security).weight roots =
      (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight roots.1 * (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight roots.2 := rfl
open _root_.P2M60f02c0e renaming h218 → _p2mH218
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h214 (security : ℕ) (root : _root_.CurrentAFT.CycleRootExpansion.Root security)
    (score : _root_.CurrentAFT.ActualControls.SafePalette security → ℝ) :
    _root_.CurrentAFT.SelectedOrdinaryRoot.rawMassLinear security (fun sample => _root_.CurrentAFT.RootMassColumns.fiber root score sample.1 sample.2) =
      (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight root • _root_.CurrentAFT.RootMassColumns.ordinaryMassAt security root score := by
  change (∑ other, (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight other •
    (_root_.CurrentAFT.SelectedOrdinaryRoot.pushLinear (_root_.CurrentAFT.ActualControls.bodyReference security) (_root_.CurrentAFT.SelectedOrdinaryRoot.rootEmbedding security other)).comp
      (_root_.CurrentAFT.SelectedOrdinaryRoot.sliceLinear security other)) (fun sample => _root_.CurrentAFT.RootMassColumns.fiber root score sample.1 sample.2) = _
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  change (∑ other, (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight other • _root_.CurrentAFT.RootMassColumns.ordinaryMassAt security other
    (_root_.CurrentAFT.RootMassColumns.fiber root score other)) = _
  exact _p2mH220 _ (_root_.CurrentAFT.RootMassColumns.ordinaryMassAt security) root score
open _root_.P2M60f02c0e renaming h214 → _p2mH214
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h219 (security : ℕ) (role : _root_.CurrentAFT.UniformBodyProfiles.BodyRole) (queue : ℤ)
    (root : _root_.CurrentAFT.CycleRootExpansion.Root security) :
    _root_.CurrentAFT.RootTaggedLocal.rootMass security role queue (Pi.single root 1) =
      (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight root • _root_.CurrentAFT.RootTaggedLocal.deviationProfile security role queue root := by
  funext color
  simp [_root_.CurrentAFT.RootTaggedLocal.rootMass, Pi.single_apply]
open _root_.P2M60f02c0e renaming h219 → _p2mH219
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h213 (security : ℕ) (root : _root_.CurrentAFT.CycleRootExpansion.Root security) :
    _root_.CurrentAFT.RootTaggedLegHigher.rawMassLinear security (Pi.single root 1) =
      (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight root • (_root_.CurrentAFT.ActualBlockFock.primaryLawAt security root.val).weight := by
  funext word
  simp [_root_.CurrentAFT.RootTaggedLegHigher.rawMassLinear, Pi.single_apply]
open _root_.P2M60f02c0e renaming h213 → _p2mH213
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h212 (security : ℕ) (root : _root_.CurrentAFT.CycleRootExpansion.Root security) :
    _root_.CurrentAFT.RootTaggedLegHigher.massLinear security (Pi.single root 1) =
      (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight root •
        ((_root_.CurrentAFT.ActualBlockFock.primaryLawAt security root.val).weight -
          _root_.CurrentAFT.RootTaggedLegHigher.rawMassLinear security (fun _ => 1)) := by
  have hcenter : _root_.AFT.TensorChannel.center (_root_.CurrentAFT.CycleRootExpansion.rootReference security) (Pi.single root 1) =
      Pi.single root 1 - (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight root • (fun _ => (1 : ℝ)) := by
    funext other
    simp only [_root_.AFT.TensorChannel.center_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one]
    congr 1
    simp [_root_.AFT.FiniteDist.expectation, Pi.single_apply]
  rw [_root_.CurrentAFT.RootTaggedLegHigher.massLinear, LinearMap.comp_apply, hcenter, map_sub, map_smul,
    _p2mH213, smul_sub]
open _root_.P2M60f02c0e renaming h212 → _p2mH212
end
open _root_.P2M60f02c0e renaming h212 → _p2mH212
open _root_.P2M60f02c0e renaming h213 → _p2mH213
open _root_.P2M60f02c0e renaming h214 → _p2mH214
open _root_.P2M60f02c0e renaming h215 → _p2mH215
open _root_.P2M60f02c0e renaming h216 → _p2mH216
open _root_.P2M60f02c0e renaming h217 → _p2mH217
open _root_.P2M60f02c0e renaming h218 → _p2mH218
open _root_.P2M60f02c0e renaming h219 → _p2mH219
open _root_.P2M60f02c0e renaming h220 → _p2mH220
end CurrentAFT.RootMassColumns
open _root_.P2M60f02c0e renaming h212 → _p2mH212
open _root_.P2M60f02c0e renaming h213 → _p2mH213
open _root_.P2M60f02c0e renaming h214 → _p2mH214
open _root_.P2M60f02c0e renaming h215 → _p2mH215
open _root_.P2M60f02c0e renaming h216 → _p2mH216
open _root_.P2M60f02c0e renaming h217 → _p2mH217
open _root_.P2M60f02c0e renaming h218 → _p2mH218
open _root_.P2M60f02c0e renaming h219 → _p2mH219
open _root_.P2M60f02c0e renaming h220 → _p2mH220
end
open _root_.P2M60f02c0e renaming h212 → _p2mH212
open _root_.P2M60f02c0e renaming h213 → _p2mH213
open _root_.P2M60f02c0e renaming h214 → _p2mH214
open _root_.P2M60f02c0e renaming h215 → _p2mH215
open _root_.P2M60f02c0e renaming h216 → _p2mH216
open _root_.P2M60f02c0e renaming h217 → _p2mH217
open _root_.P2M60f02c0e renaming h218 → _p2mH218
open _root_.P2M60f02c0e renaming h219 → _p2mH219
open _root_.P2M60f02c0e renaming h220 → _p2mH220
namespace CurrentAFT.ActualRootProjectionData
end CurrentAFT.ActualRootProjectionData
namespace CurrentAFT.ActualRootProjectionData.unprojectedChannel
end CurrentAFT.ActualRootProjectionData.unprojectedChannel
namespace CurrentAFT.RootMassColumns
end CurrentAFT.RootMassColumns
namespace CurrentAFT.RootMassColumns.fiber
end CurrentAFT.RootMassColumns.fiber
namespace CurrentAFT.RootMassColumns.primaryMassAt
end CurrentAFT.RootMassColumns.primaryMassAt
section
namespace CurrentAFT.RootReferenceColumns
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion
  ControlCoordinates GradedControlAlgebra CoefficientHilbert
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RootReferenceColumns.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RootReferenceColumns.safeDecidableEq
attribute [local irreducible] Parameters.base primaryLaw bodyReference rootReference
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h238 (security : ℕ) (source : _root_.CurrentAFT.RootPrimaryGroupedChannel.Input security) :
    _root_.CurrentAFT.RootTaggedSelectedChannel.curryLinear security
      (_root_.CurrentAFT.RootPrimaryGroupedChannel.pairLinear security (Pi.single source 1)) =
        _root_.CurrentAFT.RootMassColumns.fiber (_root_.CurrentAFT.RootPrimaryGroupedChannel.pairEquiv security source.1) (Pi.single source.2 1) := by
  funext roots primaryColor
  change (Pi.single (M := fun _ : _root_.CurrentAFT.RootPrimaryGroupedChannel.Input security => ℝ) source (1 : ℝ))
    ((_root_.CurrentAFT.RootPrimaryGroupedChannel.pairEquiv security).symm roots, primaryColor) = _
  have hroot : (_root_.CurrentAFT.RootPrimaryGroupedChannel.pairEquiv security).symm roots = source.1 ↔
      roots = _root_.CurrentAFT.RootPrimaryGroupedChannel.pairEquiv security source.1 := by
    constructor
    · intro h
      simpa using congrArg (_root_.CurrentAFT.RootPrimaryGroupedChannel.pairEquiv security) h
    · intro h
      rw [h, Equiv.symm_apply_apply]
  by_cases hr : roots = _root_.CurrentAFT.RootPrimaryGroupedChannel.pairEquiv security source.1
  · have hpair : ((_root_.CurrentAFT.RootPrimaryGroupedChannel.pairEquiv security).symm roots, primaryColor) = source ↔
        primaryColor = source.2 := by
      constructor
      · exact congrArg Prod.snd
      · intro hp
        exact Prod.ext (hroot.mpr hr) hp
    simp only [_root_.CurrentAFT.RootMassColumns.fiber, if_pos hr, Pi.single_apply, hpair]
  · have hpair : ((_root_.CurrentAFT.RootPrimaryGroupedChannel.pairEquiv security).symm roots, primaryColor) ≠ source := by
      intro h
      exact hr (hroot.mp (congrArg Prod.fst h))
    simp only [_root_.CurrentAFT.RootMassColumns.fiber, if_neg hr, Pi.single_eq_of_ne hpair, Pi.zero_apply]
open _root_.P2M60f02c0e renaming h238 → _p2mH238
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h236 (security : ℕ) (roots : _root_.CurrentAFT.RootTaggedSelected.RootPair security)
    (score : _root_.CurrentAFT.ActualControls.Palette security → ℝ) :
    _root_.CurrentAFT.RootTaggedSelectedChannel.controlCenterLinear security (_root_.CurrentAFT.RootMassColumns.fiber roots score) =
      _root_.CurrentAFT.RootMassColumns.fiber roots (_root_.CurrentAFT.CoefficientHilbert.centerLinear (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) score) := by
  funext other primaryColor
  change _root_.CurrentAFT.CoefficientHilbert.centerLinear (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.RootMassColumns.fiber roots score other) primaryColor = _
  by_cases hequal : other = roots
  · subst other
    simp [_root_.CurrentAFT.RootMassColumns.fiber]
  · simp [_root_.CurrentAFT.RootMassColumns.fiber, hequal, map_zero]
open _root_.P2M60f02c0e renaming h236 → _p2mH236
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h237 (security order : ℕ) (source : _root_.CurrentAFT.RootPrimaryGroupedChannel.Input security) :
    _root_.CurrentAFT.RootTaggedSelectedChannel.channel security order
      (_root_.CurrentAFT.RootPrimaryGroupedChannel.pairLinear security (Pi.single source 1)) =
      ((_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight (source.1 0) * (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight (source.1 1)) •
        _root_.CurrentAFT.RootReferenceColumns.primaryAt security order (_root_.CurrentAFT.RootPrimaryGroupedChannel.pairEquiv security source.1) source.2 := by
  change _root_.CurrentAFT.RootTaggedSelectedChannel.responseLinear security order
    (_root_.CurrentAFT.RootTaggedSelectedChannel.controlCenterLinear security
      (_root_.CurrentAFT.RootTaggedSelectedChannel.curryLinear security
        (_root_.CurrentAFT.RootPrimaryGroupedChannel.pairLinear security (Pi.single source 1)))) = _
  rw [_p2mH238, _p2mH236, _p2mH217,
    _p2mH218]
  rfl
open _root_.P2M60f02c0e renaming h237 → _p2mH237
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h228 (security : ℕ) (root : _root_.CurrentAFT.CycleRootExpansion.Root security) (score : _root_.CurrentAFT.ActualControls.SafePalette security → ℝ) :
    _root_.CurrentAFT.SelectedOrdinaryRoot.controlCenterLinear security (_root_.CurrentAFT.RootReferenceColumns.ordinaryFiber security root score) =
      _root_.CurrentAFT.RootReferenceColumns.ordinaryFiber security root (_root_.CurrentAFT.CoefficientHilbert.centerLinear (_root_.CurrentAFT.ActualControls.bodyReference security) score) := by
  funext sample
  change _root_.CurrentAFT.CoefficientHilbert.centerLinear (_root_.CurrentAFT.ActualControls.bodyReference security) (_root_.CurrentAFT.RootMassColumns.fiber root score sample.1) sample.2 = _
  by_cases hequal : sample.1 = root
  · simp [_root_.CurrentAFT.RootMassColumns.fiber, _root_.CurrentAFT.RootReferenceColumns.ordinaryFiber, hequal]
  · simp [_root_.CurrentAFT.RootMassColumns.fiber, _root_.CurrentAFT.RootReferenceColumns.ordinaryFiber, hequal, map_zero]
open _root_.P2M60f02c0e renaming h228 → _p2mH228
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h234 (security : ℕ) (root : _root_.CurrentAFT.CycleRootExpansion.Root security) (score : _root_.CurrentAFT.ActualControls.SafePalette security → ℝ) :
    _root_.CurrentAFT.SelectedOrdinaryRoot.densityLinear security (_root_.CurrentAFT.RootReferenceColumns.ordinaryFiber security root score) =
      (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight root • _root_.CurrentAFT.RootReferenceColumns.ordinaryDensityAt security root score := by
  change _root_.CurrentAFT.PrimaryTensorInverse.densityInverse security
    (_root_.CurrentAFT.RootTaggedLocal.profileDensity security
      (_root_.CurrentAFT.SelectedOrdinaryRoot.rawMassLinear security
        (_root_.CurrentAFT.SelectedOrdinaryRoot.controlCenterLinear security (_root_.CurrentAFT.RootReferenceColumns.ordinaryFiber security root score)))) = _
  rw [_p2mH228]
  unfold _root_.CurrentAFT.RootReferenceColumns.ordinaryFiber
  rw [_p2mH214, map_smul, map_smul]
  rfl
open _root_.P2M60f02c0e renaming h234 → _p2mH234
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h229 (security order : ℕ) (horder : 1 ≤ order) (root : _root_.CurrentAFT.CycleRootExpansion.Root security)
    (score : _root_.CurrentAFT.ActualControls.SafePalette security → ℝ) :
    _root_.CurrentAFT.SelectedOrdinaryRoot.channel security order horder (_root_.CurrentAFT.RootReferenceColumns.ordinaryFiber security root score) =
      (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight root • _root_.CurrentAFT.RootReferenceColumns.ordinaryAt security order horder root score := by
  have hcentered : _root_.CurrentAFT.SelectedOrdinaryRoot.centeredDensityLinear security (_root_.CurrentAFT.RootReferenceColumns.ordinaryFiber security root score) =
      (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight root •
        (⟨_root_.CurrentAFT.RootReferenceColumns.ordinaryDensityAt security root score, _root_.CurrentAFT.RootReferenceColumns.ordinaryDensityAt_mean security root score⟩ :
          _root_.CurrentAFT.LocalRaisingLinear.centeredScores security) := by
    apply Subtype.ext
    exact _p2mH234 security root score
  change _root_.CurrentAFT.LocalRaisingLinear.primaryEmbeddingLinear security order horder
    (_root_.CurrentAFT.SelectedOrdinaryRoot.centeredDensityLinear security (_root_.CurrentAFT.RootReferenceColumns.ordinaryFiber security root score)) * _ = _
  rw [hcentered, map_smul, smul_mul_assoc]
  rfl
open _root_.P2M60f02c0e renaming h229 → _p2mH229
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h235 (security : ℕ) (root : _root_.CurrentAFT.CycleRootExpansion.Root security) (score : _root_.CurrentAFT.ActualControls.SafePalette security → ℝ) :
    _root_.CurrentAFT.SelectedOrdinaryMean.rootMean security (_root_.CurrentAFT.RootReferenceColumns.ordinaryFiber security root score) =
      (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight root • score := by
  funext centerColor
  simp [_root_.CurrentAFT.SelectedOrdinaryMean.rootMean, _root_.CurrentAFT.RootReferenceColumns.ordinaryFiber, _root_.CurrentAFT.RootMassColumns.fiber, _root_.AFT.FiniteDist.expectation, ite_apply]
open _root_.P2M60f02c0e renaming h235 → _p2mH235
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h232 (security : ℕ) (score : _root_.CurrentAFT.ActualControls.SafePalette security → ℝ) :
    _root_.CurrentAFT.SelectedOrdinaryMean.constantRoot security score = ∑ root, _root_.CurrentAFT.RootReferenceColumns.ordinaryFiber security root score := by
  funext sample
  simp [_root_.CurrentAFT.SelectedOrdinaryMean.constantRoot, _root_.CurrentAFT.RootReferenceColumns.ordinaryFiber, _root_.CurrentAFT.RootMassColumns.fiber, ite_apply]
open _root_.P2M60f02c0e renaming h232 → _p2mH232
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h231 (security order : ℕ) (horder : 1 ≤ order) (score : _root_.CurrentAFT.ActualControls.SafePalette security → ℝ) :
    _root_.CurrentAFT.SelectedOrdinaryRoot.channel security order horder (_root_.CurrentAFT.SelectedOrdinaryMean.constantRoot security score) =
      ∑ root, (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight root • _root_.CurrentAFT.RootReferenceColumns.ordinaryAt security order horder root score := by
  rw [_p2mH232, map_sum]
  simp only [_p2mH229]
open _root_.P2M60f02c0e renaming h231 → _p2mH231
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h225 (security order : ℕ) (horder : 1 ≤ order) (root : _root_.CurrentAFT.CycleRootExpansion.Root security)
    (score : _root_.CurrentAFT.ActualControls.SafePalette security → ℝ) :
    _root_.CurrentAFT.SelectedOrdinaryHybrid.channel security order horder (_root_.CurrentAFT.RootReferenceColumns.ordinaryFiber security root score) =
      (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight root • _root_.CurrentAFT.RootReferenceColumns.hybridAt security order horder root score := by
  have hcenter : _root_.CurrentAFT.SelectedOrdinaryMean.rootCenter security (_root_.CurrentAFT.RootReferenceColumns.ordinaryFiber security root score) =
      _root_.CurrentAFT.RootReferenceColumns.ordinaryFiber security root score - _root_.CurrentAFT.SelectedOrdinaryMean.constantRoot security
        ((_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight root • score) := by
    change _root_.CurrentAFT.RootReferenceColumns.ordinaryFiber security root score - _root_.CurrentAFT.SelectedOrdinaryMean.constantRoot security
      (_root_.CurrentAFT.SelectedOrdinaryMean.rootMean security (_root_.CurrentAFT.RootReferenceColumns.ordinaryFiber security root score)) = _
    rw [_p2mH235]
  rw [_root_.CurrentAFT.SelectedOrdinaryHybrid.channel_apply, hcenter, _p2mH235, map_smul]
  rw [map_sub, map_smul, map_smul, _p2mH229, _p2mH231]
  unfold _root_.CurrentAFT.RootReferenceColumns.hybridAt
  rw [smul_sub, smul_add]
  abel
open _root_.P2M60f02c0e renaming h225 → _p2mH225
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h240 (security order : ℕ) (horder : 1 ≤ order)
    (role : _root_.CurrentAFT.UniformBodyProfiles.BodyRole) (queue : ℤ) (root : _root_.CurrentAFT.CycleRootExpansion.Root security) :
    _root_.CurrentAFT.RootTaggedFamilies.rootFamilyLinear security order horder role queue (Pi.single root 1) =
      (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight root • _root_.CurrentAFT.RootReferenceColumns.singletonFirstAt security order horder role queue root := by
  have hlift : _root_.CurrentAFT.RootTaggedLocal.rootLift security role queue (Pi.single root 1) =
      (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight root • _root_.CurrentAFT.RootReferenceColumns.singletonDensityAt security role queue root := by
    rw [_root_.CurrentAFT.RootTaggedLocal.rootLift_apply, _p2mH219, map_smul, map_smul]
    rfl
  have hs : (⟨_root_.CurrentAFT.RootTaggedLocal.rootLift security role queue (Pi.single root 1),
      _root_.CurrentAFT.RootTaggedLocal.rootLift_mean security role queue (Pi.single root 1)⟩ : _root_.CurrentAFT.LocalRaisingLinear.centeredScores security) =
      (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight root •
        (⟨_root_.CurrentAFT.RootReferenceColumns.singletonDensityAt security role queue root, _root_.CurrentAFT.RootReferenceColumns.singletonDensityAt_mean security role queue root⟩ :
          _root_.CurrentAFT.LocalRaisingLinear.centeredScores security) := by
    apply Subtype.ext
    exact hlift
  rw [_root_.CurrentAFT.RootTaggedFamilies.rootFamilyLinear_apply]
  change _root_.CurrentAFT.LocalRaisingLinear.primaryEmbeddingLinear security order horder
    (⟨_root_.CurrentAFT.RootTaggedLocal.rootLift security role queue (Pi.single root 1),
      _root_.CurrentAFT.RootTaggedLocal.rootLift_mean security role queue (Pi.single root 1)⟩ : _root_.CurrentAFT.LocalRaisingLinear.centeredScores security) = _
  rw [hs, map_smul]
  rfl
open _root_.P2M60f02c0e renaming h240 → _p2mH240
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h239 (security order : ℕ) (horder : 1 ≤ order)
    (role : _root_.CurrentAFT.UniformBodyProfiles.BodyRole) (queue : ℤ) (root : _root_.CurrentAFT.CycleRootExpansion.Root security) :
    _root_.CurrentAFT.RootUnselectedChannels.singletonChannel security order horder role queue (Pi.single root 1) =
      (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight root • _root_.CurrentAFT.RootReferenceColumns.singletonAt security order horder role queue root := by
  change _root_.CurrentAFT.RootTaggedFamilies.rootFamilyLinear security order horder role queue (Pi.single root 1) * _ = _
  rw [_p2mH240, smul_mul_assoc]
  rfl
open _root_.P2M60f02c0e renaming h239 → _p2mH239
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h227 (security order : ℕ) (root : _root_.CurrentAFT.CycleRootExpansion.Root security) :
    _root_.CurrentAFT.RootLegCoefficientLinear.rootHigherLinear security order (Pi.single root 1) =
      (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight root • _root_.CurrentAFT.RootReferenceColumns.legHigherAt security order root := by
  change _root_.CurrentAFT.RootLegCoefficientLinear.higherFamilyLinear security order
    (_root_.CurrentAFT.RootTaggedLegHigher.massLinear security (Pi.single root 1)) = _
  rw [_p2mH212, map_smul]
  rfl
open _root_.P2M60f02c0e renaming h227 → _p2mH227
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h226 (security order : ℕ) (horder : 1 ≤ order) (root : _root_.CurrentAFT.CycleRootExpansion.Root security) :
    _root_.CurrentAFT.RootUnselectedChannels.legChannel security order horder (Pi.single root 1) =
      (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight root • _root_.CurrentAFT.RootReferenceColumns.legAt security order horder root := by
  change (_root_.CurrentAFT.RootTaggedFamilies.rootFamilyLinear security order horder .attachment 0 (Pi.single root 1) +
    _root_.CurrentAFT.RootLegCoefficientLinear.rootHigherLinear security order (Pi.single root 1)) * _ = _
  rw [_p2mH240, _p2mH227, ← smul_add, smul_mul_assoc]
  rfl
open _root_.P2M60f02c0e renaming h226 → _p2mH226
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h242 (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (block : _root_.CurrentAFT.ActualBlockFock.BlockIndex security) (root : _root_.CurrentAFT.CycleRootExpansion.Root security) :
    _root_.CurrentAFT.RootUnselectedBlockChannel.channel security order horder queue block (Pi.single root 1) =
      (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight root • _root_.CurrentAFT.RootReferenceColumns.unselectedAt security order horder queue block root := by
  rcases block with leg | single
  · exact _p2mH226 security order horder root
  · rcases single with center | point
    · exact _p2mH239 security order horder .free 0 root
    · exact _p2mH239 security order horder .queue queue root
open _root_.P2M60f02c0e renaming h242 → _p2mH242
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h233 (security : ℕ) (source : _root_.CurrentAFT.RootOrdinaryGroupedChannel.Input security) :
    _root_.CurrentAFT.RootOrdinaryGroupedChannel.toRaw security (Pi.single source 1) =
      _root_.CurrentAFT.RootReferenceColumns.ordinaryFiber security (source.1 0) (Pi.single source.2 1) := by
  funext sample
  change (Pi.single (M := fun _ : _root_.CurrentAFT.RootOrdinaryGroupedChannel.Input security => ℝ) source 1)
    ((fun _ => sample.1), sample.2) = _
  have hroots : (fun _ : Fin 1 => sample.1) = source.1 ↔ sample.1 = source.1 0 := by
    constructor
    · intro h
      exact congrFun h 0
    · intro h
      funext index
      rw [Fin.eq_zero index]
      exact h
  have hpair : ((fun _ : Fin 1 => sample.1), sample.2) = source ↔
      sample.1 = source.1 0 ∧ sample.2 = source.2 := by
    rw [Prod.ext_iff, hroots]
  by_cases hr : sample.1 = source.1 0
  · have hpair' : ((fun _ : Fin 1 => sample.1), sample.2) = source ↔ sample.2 = source.2 := by
      constructor
      · intro h
        exact (hpair.mp h).2
      · intro h
        exact hpair.mpr ⟨hr, h⟩
    simp only [_root_.CurrentAFT.RootReferenceColumns.ordinaryFiber, _root_.CurrentAFT.RootMassColumns.fiber, if_pos hr, Pi.single_apply, hpair']
  · have hpair' : ((fun _ : Fin 1 => sample.1), sample.2) ≠ source := fun h => hr (hpair.mp h).1
    simp only [_root_.CurrentAFT.RootReferenceColumns.ordinaryFiber, _root_.CurrentAFT.RootMassColumns.fiber, if_neg hr, Pi.zero_apply, Pi.single_eq_of_ne hpair']
open _root_.P2M60f02c0e renaming h233 → _p2mH233
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h230 (security order : ℕ) (horder : 1 ≤ order) (source : _root_.CurrentAFT.RootOrdinaryGroupedChannel.Input security) :
    _root_.CurrentAFT.SelectedOrdinaryHybrid.channel security order horder
      (_root_.CurrentAFT.RootOrdinaryGroupedChannel.toRaw security (Pi.single source 1)) =
      (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight (source.1 0) •
        _root_.CurrentAFT.RootReferenceColumns.hybridAt security order horder (source.1 0) (Pi.single source.2 1) := by
  rw [_p2mH233]
  exact _p2mH225 security order horder _ _
open _root_.P2M60f02c0e renaming h230 → _p2mH230
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h243 (security : ℕ) (source : _root_.CurrentAFT.RootUnselectedGrouped.Input security) :
    _root_.CurrentAFT.RootUnselectedGrouped.extractLinear security (Pi.single source 1) = Pi.single (source.1 0) 1 := by
  funext root
  change (Pi.single (M := fun _ : _root_.CurrentAFT.RootUnselectedGrouped.Input security => ℝ) source 1)
    ((_root_.CurrentAFT.RootUnselectedGrouped.inputEquiv security).symm root) = _
  have hequal : (_root_.CurrentAFT.RootUnselectedGrouped.inputEquiv security).symm root = source ↔ root = source.1 0 := by
    constructor
    · intro h
      have h' := congrArg (_root_.CurrentAFT.RootUnselectedGrouped.inputEquiv security) h
      calc
        root = _root_.CurrentAFT.RootUnselectedGrouped.inputEquiv security source := by
          simpa only [Equiv.apply_symm_apply] using h'
        _ = source.1 0 := rfl
    · intro h
      change _ = _
      rw [show source.1 0 = _root_.CurrentAFT.RootUnselectedGrouped.inputEquiv security source from rfl] at h
      rw [h, Equiv.symm_apply_apply]
  simp only [Pi.single_apply, hequal]
open _root_.P2M60f02c0e renaming h243 → _p2mH243
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h244 (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (block : _root_.CurrentAFT.ActualBlockFock.BlockIndex security) (source : _root_.CurrentAFT.RootUnselectedGrouped.Input security) :
    _root_.CurrentAFT.RootUnselectedGrouped.channel security order horder queue block (Pi.single source 1) =
      (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight (source.1 0) • _root_.CurrentAFT.RootReferenceColumns.unselectedAt security order horder queue block (source.1 0) := by
  change _root_.CurrentAFT.RootUnselectedBlockChannel.channel security order horder queue block
    (_root_.CurrentAFT.RootUnselectedGrouped.extractLinear security (Pi.single source 1)) = _
  rw [_p2mH243]
  exact _p2mH242 security order horder queue block _
open _root_.P2M60f02c0e renaming h244 → _p2mH244
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h241 {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s) (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security))
    (group : _root_.CurrentAFT.PairedRootPlacement.ActiveGroup selection tagged)
    (source : _root_.CurrentAFT.ActualRootGroupedChannel.Input selection tagged group) :
    _root_.CurrentAFT.ActualRootProjectionData.unprojectedChannel order horder queue selection tagged group (Pi.single source 1) =
      (∏ slot, (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight (source.1 slot)) •
        _root_.CurrentAFT.RootReferenceColumns.reducedColumn order horder queue selection tagged group source := by
  rcases group with (primary | ordinary) | kept
  · have hprod : (∏ slot, (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight (source.1 slot)) =
        (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight (source.1 (0 : Fin 2)) * (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight (source.1 (1 : Fin 2)) := by
      calc
        _ = ∏ slot : Fin 2, (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight (source.1 slot) :=
          Finset.prod_congr (by ext; simp) (fun _ _ => rfl)
        _ = _ := Fin.prod_univ_two _
    rw [hprod]
    exact _p2mH237 security order source
  · have hprod : (∏ slot, (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight (source.1 slot)) =
        (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight (source.1 (0 : Fin 1)) := by
      calc
        _ = ∏ slot : Fin 1, (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight (source.1 slot) :=
          Finset.prod_congr (by
            ext index
            have hi : (index : Fin 1) = (0 : Fin 1) := @Subsingleton.elim (Fin 1) inferInstance index 0
            subst index
            simp) (fun _ _ => rfl)
        _ = _ := Fin.prod_univ_one _
    rw [hprod]
    exact _p2mH230 security order horder source
  · have hprod : (∏ slot, (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight (source.1 slot)) =
        (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight (source.1 (0 : Fin 1)) := by
      calc
        _ = ∏ slot : Fin 1, (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight (source.1 slot) :=
          Finset.prod_congr (by
            ext index
            have hi : (index : Fin 1) = (0 : Fin 1) := @Subsingleton.elim (Fin 1) inferInstance index 0
            subst index
            simp) (fun _ _ => rfl)
        _ = _ := Fin.prod_univ_one _
    rw [hprod]
    have hdelta : (Pi.single (M := fun _ : _root_.CurrentAFT.ActualRootGroupedChannel.Input selection tagged (.inr kept) => ℝ) source 1) =
        (Pi.single (M := fun _ : _root_.CurrentAFT.RootUnselectedGrouped.Input security => ℝ) source 1) := by
      funext word
      by_cases hequal : word = source <;> simp only [Pi.single_apply, hequal, if_true, if_false]
    rw [hdelta]
    exact _p2mH244 security order horder queue kept.val.val source
open _root_.P2M60f02c0e renaming h241 → _p2mH241
end
open _root_.P2M60f02c0e renaming h225 → _p2mH225
open _root_.P2M60f02c0e renaming h226 → _p2mH226
open _root_.P2M60f02c0e renaming h227 → _p2mH227
open _root_.P2M60f02c0e renaming h228 → _p2mH228
open _root_.P2M60f02c0e renaming h229 → _p2mH229
open _root_.P2M60f02c0e renaming h230 → _p2mH230
open _root_.P2M60f02c0e renaming h231 → _p2mH231
open _root_.P2M60f02c0e renaming h232 → _p2mH232
open _root_.P2M60f02c0e renaming h233 → _p2mH233
open _root_.P2M60f02c0e renaming h234 → _p2mH234
open _root_.P2M60f02c0e renaming h235 → _p2mH235
open _root_.P2M60f02c0e renaming h236 → _p2mH236
open _root_.P2M60f02c0e renaming h237 → _p2mH237
open _root_.P2M60f02c0e renaming h238 → _p2mH238
open _root_.P2M60f02c0e renaming h239 → _p2mH239
open _root_.P2M60f02c0e renaming h240 → _p2mH240
open _root_.P2M60f02c0e renaming h241 → _p2mH241
open _root_.P2M60f02c0e renaming h242 → _p2mH242
open _root_.P2M60f02c0e renaming h243 → _p2mH243
open _root_.P2M60f02c0e renaming h244 → _p2mH244
end CurrentAFT.RootReferenceColumns
open _root_.P2M60f02c0e renaming h225 → _p2mH225
open _root_.P2M60f02c0e renaming h226 → _p2mH226
open _root_.P2M60f02c0e renaming h227 → _p2mH227
open _root_.P2M60f02c0e renaming h228 → _p2mH228
open _root_.P2M60f02c0e renaming h229 → _p2mH229
open _root_.P2M60f02c0e renaming h230 → _p2mH230
open _root_.P2M60f02c0e renaming h231 → _p2mH231
open _root_.P2M60f02c0e renaming h232 → _p2mH232
open _root_.P2M60f02c0e renaming h233 → _p2mH233
open _root_.P2M60f02c0e renaming h234 → _p2mH234
open _root_.P2M60f02c0e renaming h235 → _p2mH235
open _root_.P2M60f02c0e renaming h236 → _p2mH236
open _root_.P2M60f02c0e renaming h237 → _p2mH237
open _root_.P2M60f02c0e renaming h238 → _p2mH238
open _root_.P2M60f02c0e renaming h239 → _p2mH239
open _root_.P2M60f02c0e renaming h240 → _p2mH240
open _root_.P2M60f02c0e renaming h241 → _p2mH241
open _root_.P2M60f02c0e renaming h242 → _p2mH242
open _root_.P2M60f02c0e renaming h243 → _p2mH243
open _root_.P2M60f02c0e renaming h244 → _p2mH244
end
open _root_.P2M60f02c0e renaming h225 → _p2mH225
open _root_.P2M60f02c0e renaming h226 → _p2mH226
open _root_.P2M60f02c0e renaming h227 → _p2mH227
open _root_.P2M60f02c0e renaming h228 → _p2mH228
open _root_.P2M60f02c0e renaming h229 → _p2mH229
open _root_.P2M60f02c0e renaming h230 → _p2mH230
open _root_.P2M60f02c0e renaming h231 → _p2mH231
open _root_.P2M60f02c0e renaming h232 → _p2mH232
open _root_.P2M60f02c0e renaming h233 → _p2mH233
open _root_.P2M60f02c0e renaming h234 → _p2mH234
open _root_.P2M60f02c0e renaming h235 → _p2mH235
open _root_.P2M60f02c0e renaming h236 → _p2mH236
open _root_.P2M60f02c0e renaming h237 → _p2mH237
open _root_.P2M60f02c0e renaming h238 → _p2mH238
open _root_.P2M60f02c0e renaming h239 → _p2mH239
open _root_.P2M60f02c0e renaming h240 → _p2mH240
open _root_.P2M60f02c0e renaming h241 → _p2mH241
open _root_.P2M60f02c0e renaming h242 → _p2mH242
open _root_.P2M60f02c0e renaming h243 → _p2mH243
open _root_.P2M60f02c0e renaming h244 → _p2mH244
namespace CurrentAFT.RootReferenceColumns
end CurrentAFT.RootReferenceColumns
namespace CurrentAFT.RootReferenceColumns.ordinaryAt
end CurrentAFT.RootReferenceColumns.ordinaryAt
namespace CurrentAFT.RootReferenceColumns.ordinaryDensityAt
end CurrentAFT.RootReferenceColumns.ordinaryDensityAt
namespace CurrentAFT.RootReferenceColumns.ordinaryFiber
end CurrentAFT.RootReferenceColumns.ordinaryFiber
namespace CurrentAFT.RootReferenceColumns.reducedColumn
end CurrentAFT.RootReferenceColumns.reducedColumn
namespace CurrentAFT.RootReferenceColumns.singletonDensityAt
end CurrentAFT.RootReferenceColumns.singletonDensityAt
namespace CurrentAFT.RootReferenceColumns.unselectedAt
end CurrentAFT.RootReferenceColumns.unselectedAt
namespace CurrentAFT.SelectedOrdinaryMean
end CurrentAFT.SelectedOrdinaryMean
namespace CurrentAFT.SelectedOrdinaryMean.constantRoot
end CurrentAFT.SelectedOrdinaryMean.constantRoot
namespace CurrentAFT.SelectedOrdinaryMean.rootMean
end CurrentAFT.SelectedOrdinaryMean.rootMean
namespace CurrentAFT.SelectedOrdinaryRoot
end CurrentAFT.SelectedOrdinaryRoot
namespace CurrentAFT.SelectedOrdinaryRoot.channel
end CurrentAFT.SelectedOrdinaryRoot.channel
section
namespace CurrentAFT.RootWeightedSynthesis
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  CycleRootExpansion ControlCoordinates GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RootWeightedSynthesis.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RootWeightedSynthesis.nativeVertexDecidableEq
attribute [local instance] _root_.CurrentAFT.RootWeightedSynthesis.classicalSumDecidableEq
attribute [local instance] _root_.CurrentAFT.RootWeightedSynthesis.classicalProdDecidableEq
attribute [local instance] _root_.CurrentAFT.RootWeightedSynthesis.classicalSigmaDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount rootReference
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h252 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (source : _root_.CurrentAFT.PairedRootInput.GroupInput selection tagged) :
    (∏ group, ∏ slot, (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight ((source group).1 slot)) =
      (∏ index, (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight (_root_.CurrentAFT.RootWeightedSynthesis.taggedOutput selection tagged source index)) *
        _root_.CurrentAFT.RootWeightedSynthesis.untaggedWeight selection tagged source := by
  have h := Finset.prod_mul_prod_compl (Finset.univ.map (_root_.CurrentAFT.PairedRootInput.sourceEmbedding selection tagged))
    (fun slot : _root_.CurrentAFT.RootWeightedSynthesis.RootSlot selection tagged => (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight ((source slot.fst).1 slot.snd))
  simpa only [Finset.prod_map, Fintype.prod_sigma, _root_.CurrentAFT.RootWeightedSynthesis.taggedOutput, _root_.CurrentAFT.RootWeightedSynthesis.untaggedWeight] using h.symm
open _root_.P2M60f02c0e renaming h252 → _p2mH252
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h254 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s)
    (source : _root_.CurrentAFT.PairedRootInput.GroupInput selection tagged) :
    _root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel source *
        (∏ group, ∏ slot, (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight ((source group).1 slot)) =
      _root_.CurrentAFT.PairedRootInput.controlKernel selection tagged kernel (fun group => (source group).2) *
        _root_.CurrentAFT.RootWeightedSynthesis.untaggedWeight selection tagged source * _root_.CurrentAFT.RootWeightedSynthesis.weightedCoefficient selection tagged layout source := by
  letI : DecidableEq (Fin tagged.card) := instDecidableEqFin _
  have h := _p2mH245 security tagged.card (_root_.CurrentAFT.PairedRootInput.labels tagged layout)
    (_root_.CurrentAFT.RootWeightedSynthesis.taggedOutput selection tagged source)
  rw [_root_.AFT.FiniteDist.expectation_map] at h
  change (∏ index, (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight (_root_.CurrentAFT.RootWeightedSynthesis.taggedOutput selection tagged source index)) *
    _root_.CurrentAFT.CycleRootExpansion.selectedCoefficient security tagged.card (_root_.CurrentAFT.PairedRootInput.labels tagged layout) (_root_.CurrentAFT.RootWeightedSynthesis.taggedOutput selection tagged source) =
      _root_.CurrentAFT.RootWeightedSynthesis.weightedCoefficient selection tagged layout source at h
  rw [← h, _p2mH252]
  unfold _root_.CurrentAFT.PairedRootInput.jointInput
  change _root_.CurrentAFT.CycleRootExpansion.selectedCoefficient security tagged.card (_root_.CurrentAFT.PairedRootInput.labels tagged layout) (_root_.CurrentAFT.RootWeightedSynthesis.taggedOutput selection tagged source) * _ * _ = _
  ring
open _root_.P2M60f02c0e renaming h254 → _p2mH254
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h253 {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s) (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security))
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.CurrentAFT.ActualRootResponse.response order horder queue selection tagged layout kernel =
      ∑ source : _root_.CurrentAFT.PairedRootInput.GroupInput selection tagged,
        (_root_.CurrentAFT.PairedRootInput.controlKernel selection tagged kernel (fun group => (source group).2) *
          _root_.CurrentAFT.RootWeightedSynthesis.untaggedWeight selection tagged source * _root_.CurrentAFT.RootWeightedSynthesis.weightedCoefficient selection tagged layout source) •
            ∏ group, _root_.CurrentAFT.RootReferenceColumns.reducedColumn order horder queue selection tagged group (source group) := by
  rw [_p2mH15, _root_.CurrentAFT.GroupedFamilyIdentity.response_eq]
  apply Finset.sum_congr rfl
  intro source _
  have hcolumn (group : _root_.CurrentAFT.PairedRootPlacement.ActiveGroup selection tagged) :
      _root_.CurrentAFT.ActualRootProjectionData.unprojectedChannel order horder queue selection tagged group
        (@Pi.single (_root_.CurrentAFT.ActualRootGroupedChannel.Input selection tagged group) (fun _ => ℝ) (fun _ => Real.instZero)
          (Classical.decEq _) (source group) 1) =
        (∏ slot, (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight ((source group).1 slot)) •
          _root_.CurrentAFT.RootReferenceColumns.reducedColumn order horder queue selection tagged group (source group) := by
    convert _p2mH241 order horder queue selection tagged group (source group) using 1
    congr 1
    funext word
    by_cases hequal : word = source group <;> simp only [Pi.single_apply, hequal, if_true, if_false]
  simp_rw [hcolumn, Finset.prod_smul, smul_smul]
  rw [_p2mH254]
open _root_.P2M60f02c0e renaming h253 → CurrentAFT.RootWeightedSynthesis.response_eq
open _root_.P2M60f02c0e renaming h253 → _p2mH253
end
open _root_.P2M60f02c0e renaming h252 → _p2mH252
open _root_.P2M60f02c0e renaming h253 → CurrentAFT.RootWeightedSynthesis.response_eq
open _root_.P2M60f02c0e renaming h253 → _p2mH253
open _root_.P2M60f02c0e renaming h254 → _p2mH254
end CurrentAFT.RootWeightedSynthesis
open _root_.P2M60f02c0e renaming h252 → _p2mH252
open _root_.P2M60f02c0e renaming h253 → CurrentAFT.RootWeightedSynthesis.response_eq
open _root_.P2M60f02c0e renaming h253 → _p2mH253
open _root_.P2M60f02c0e renaming h254 → _p2mH254
end
open _root_.P2M60f02c0e renaming h252 → _p2mH252
open _root_.P2M60f02c0e renaming h253 → CurrentAFT.RootWeightedSynthesis.response_eq
open _root_.P2M60f02c0e renaming h253 → _p2mH253
open _root_.P2M60f02c0e renaming h254 → _p2mH254
namespace CurrentAFT.CurrentRectangleIndex
end CurrentAFT.CurrentRectangleIndex
namespace CurrentAFT.CurrentRectangleIndex.decode
end CurrentAFT.CurrentRectangleIndex.decode
namespace CurrentAFT.CurrentRectangleIndex.encode
end CurrentAFT.CurrentRectangleIndex.encode
namespace CurrentAFT.CurrentRectangleIndex.paletteEquiv
end CurrentAFT.CurrentRectangleIndex.paletteEquiv
namespace CurrentAFT.CurrentRectangleIndex.safe
end CurrentAFT.CurrentRectangleIndex.safe
namespace CurrentAFT.GroupSourcePadding
end CurrentAFT.GroupSourcePadding
namespace CurrentAFT.GroupSourcePadding.Input
end CurrentAFT.GroupSourcePadding.Input
namespace CurrentAFT.GroupSourcePadding.Kind
end CurrentAFT.GroupSourcePadding.Kind
namespace CurrentAFT.GroupSourcePadding.Kind.kept
end CurrentAFT.GroupSourcePadding.Kind.kept
namespace CurrentAFT.GroupSourcePadding.Kind.ordinary
end CurrentAFT.GroupSourcePadding.Kind.ordinary
namespace CurrentAFT.GroupSourcePadding.Kind.primary
end CurrentAFT.GroupSourcePadding.Kind.primary
namespace CurrentAFT.GroupSourcePadding.Valid
end CurrentAFT.GroupSourcePadding.Valid
namespace CurrentAFT.GroupSourcePadding.encode
end CurrentAFT.GroupSourcePadding.encode
namespace CurrentAFT.GroupSourcePadding.indexDecode
end CurrentAFT.GroupSourcePadding.indexDecode
namespace CurrentAFT.GroupSourcePadding.recover
end CurrentAFT.GroupSourcePadding.recover
namespace CurrentAFT.InwardAnchor
end CurrentAFT.InwardAnchor
namespace CurrentAFT.InwardAnchor.SafeColor
end CurrentAFT.InwardAnchor.SafeColor
namespace CurrentAFT.RootWeightedSynthesis
end CurrentAFT.RootWeightedSynthesis
namespace CurrentAFT.RootWeightedSynthesis.taggedOutput
end CurrentAFT.RootWeightedSynthesis.taggedOutput
namespace CurrentAFT.RootWeightedSynthesis.untaggedWeight
end CurrentAFT.RootWeightedSynthesis.untaggedWeight
namespace CurrentAFT.RootWeightedSynthesis.weightedCoefficient
end CurrentAFT.RootWeightedSynthesis.weightedCoefficient
section
namespace CurrentAFT.CurrentGroupSourcePadding
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  GroupSourcePadding CurrentRectangleIndex
open scoped BigOperators
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.CurrentGroupSourcePadding.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.CurrentGroupSourcePadding.classicalSumDecidableEq
attribute [local instance] _root_.CurrentAFT.CurrentGroupSourcePadding.classicalSigmaDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h27 {Scalar : Type*} [AddCommMonoid Scalar] {security r s k : ℕ}
    (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s) (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security))
    (keptOrdering : Fin k ≃ _root_.CurrentAFT.PairedRootPlacement.HitKept selection tagged) (summand : _root_.CurrentAFT.PairedRootInput.GroupInput selection tagged → Scalar) :
    (∑ index : Fin ((_root_.CurrentAFT.CurrentRectangleIndex.colors security)^(((r+s)+k)*3)),
      (_root_.CurrentAFT.CurrentGroupSourcePadding.decode selection tagged keptOrdering index).elim 0 summand) = ∑ source, summand source := by
  have h := _p2mH47 (_root_.CurrentAFT.CurrentRectangleIndex.colors security) (_root_.CurrentAFT.CurrentRectangleIndex.colors_pos security) (_root_.CurrentAFT.CurrentRectangleIndex.safe security) (_root_.CurrentAFT.CurrentGroupSourcePadding.groupKind selection tagged)
    ((r+s)+k) (_root_.CurrentAFT.CurrentGroupSourcePadding.groupOrdering selection tagged keptOrdering) (summand ∘ _root_.CurrentAFT.CurrentGroupSourcePadding.sourceEquiv selection tagged)
  simpa only [_root_.CurrentAFT.CurrentGroupSourcePadding.decode, Option.elim_map, Function.comp_apply,
    Equiv.sum_comp (_root_.CurrentAFT.CurrentGroupSourcePadding.sourceEquiv selection tagged)] using h
open _root_.P2M60f02c0e renaming h27 → _p2mH27
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h26 {security r s k : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s) (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security))
    (keptOrdering : Fin k ≃ _root_.CurrentAFT.PairedRootPlacement.HitKept selection tagged)
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security)
      (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.CurrentAFT.ActualRootResponse.response order horder queue selection tagged layout kernel =
      ∑ index : Fin ((_root_.CurrentAFT.CurrentRectangleIndex.colors security)^(((r+s)+k)*3)),
        (_root_.CurrentAFT.CurrentGroupSourcePadding.decode selection tagged keptOrdering index).elim 0 (fun source =>
          (_root_.CurrentAFT.PairedRootInput.controlKernel selection tagged kernel (fun group => (source group).2) *
            _root_.CurrentAFT.RootWeightedSynthesis.untaggedWeight selection tagged source *
            _root_.CurrentAFT.RootWeightedSynthesis.weightedCoefficient selection tagged layout source) •
            ∏ group, _root_.CurrentAFT.RootReferenceColumns.reducedColumn order horder queue selection tagged group (source group)) := by
  rw [_p2mH27, _p2mH253]
open _root_.P2M60f02c0e renaming h26 → CurrentAFT.CurrentGroupSourcePadding.response_eq
open _root_.P2M60f02c0e renaming h26 → _p2mH26
end
open _root_.P2M60f02c0e renaming h26 → CurrentAFT.CurrentGroupSourcePadding.response_eq
open _root_.P2M60f02c0e renaming h26 → _p2mH26
open _root_.P2M60f02c0e renaming h27 → _p2mH27
end CurrentAFT.CurrentGroupSourcePadding
open _root_.P2M60f02c0e renaming h26 → CurrentAFT.CurrentGroupSourcePadding.response_eq
open _root_.P2M60f02c0e renaming h26 → _p2mH26
open _root_.P2M60f02c0e renaming h27 → _p2mH27
end
open _root_.P2M60f02c0e renaming h26 → CurrentAFT.CurrentGroupSourcePadding.response_eq
open _root_.P2M60f02c0e renaming h26 → _p2mH26
open _root_.P2M60f02c0e renaming h27 → _p2mH27
namespace CurrentAFT.CurrentGroupSourcePadding
end CurrentAFT.CurrentGroupSourcePadding
namespace CurrentAFT.CurrentGroupSourcePadding.decode
end CurrentAFT.CurrentGroupSourcePadding.decode
namespace CurrentAFT.CurrentGroupSourcePadding.groupKind
end CurrentAFT.CurrentGroupSourcePadding.groupKind
section
namespace CurrentAFT.CurrentRootOrdering
open AFT ActualBlockFock TaggedSelection PairedRootPlacement
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h28 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s) (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) :
    (_root_.CurrentAFT.CurrentRootOrdering.keptIndices selection tagged).card ≤ tagged.card := by
  unfold _root_.CurrentAFT.CurrentRootOrdering.keptIndices _root_.CurrentAFT.CurrentRootOrdering.tagIndices _root_.CurrentAFT.CurrentRootOrdering.keptTags
  rw [Finset.card_map]
  exact Finset.card_filter_le _ _
open _root_.P2M60f02c0e renaming h28 → _p2mH28
end CurrentAFT.CurrentRootOrdering
open _root_.P2M60f02c0e renaming h28 → _p2mH28
end
open _root_.P2M60f02c0e renaming h28 → _p2mH28
namespace CurrentAFT.ActualRootDefect
end CurrentAFT.ActualRootDefect
namespace CurrentAFT.ActualRootDefect.selectedDefect
end CurrentAFT.ActualRootDefect.selectedDefect
namespace CurrentAFT.ActualRootFamily
end CurrentAFT.ActualRootFamily
namespace CurrentAFT.ActualRootFamily.rootLinear
end CurrentAFT.ActualRootFamily.rootLinear
namespace CurrentAFT.ActualRootFamily.selectedAverage
end CurrentAFT.ActualRootFamily.selectedAverage
section
namespace CurrentAFT.FullResponseEnumeration
open AFT ActualBlockFock ControlCoordinates GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h41 {Pool : Type*} [Fintype Pool] [DecidableEq Pool]
    (order : ℕ) (subset : Finset Pool) : subset ∈ _root_.CurrentAFT.FullResponseEnumeration.boundedSubsets Pool order ↔ subset.card ≤ order := by
  constructor
  · intro hsubset
    obtain ⟨word, _, rfl⟩ := Finset.mem_image.mp hsubset
    have hc := Finset.card_image_le (s := (Finset.univ : Finset (Fin word.1.val))) (f := word.2)
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    exact hc.trans (by have := word.1.isLt; omega)
  · intro hcard
    let number : Fin subset.card ≃ subset :=
      (Fintype.equivFinOfCardEq (show Fintype.card subset = subset.card by simp)).symm
    let word : _root_.CurrentAFT.FullResponseEnumeration.SubsetWords Pool order := ⟨⟨subset.card, by omega⟩, fun index => (number index).val⟩
    refine Finset.mem_image.mpr ⟨word, Finset.mem_univ _, ?_⟩
    ext point
    constructor
    · intro hpoint
      obtain ⟨index, _, rfl⟩ := Finset.mem_image.mp hpoint
      exact (number index).property
    · intro hpoint
      refine Finset.mem_image.mpr ⟨number.symm ⟨point, hpoint⟩, Finset.mem_univ _, ?_⟩
      exact congrArg Subtype.val (number.apply_symm_apply ⟨point, hpoint⟩)
open _root_.P2M60f02c0e renaming h41 → _p2mH41
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h42 {Pool : Type*} [Fintype Pool] (order : ℕ) (hpool : 1 ≤ Fintype.card Pool) :
    Fintype.card (_root_.CurrentAFT.FullResponseEnumeration.SubsetWords Pool order) ≤ (order + 1) * (Fintype.card Pool)^order := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _size : Fin (order + 1), (Fintype.card Pool)^order := by
      apply Finset.sum_le_sum
      intro size _
      simp only [Fintype.card_fun, Fintype.card_fin]
      exact Nat.pow_le_pow_right hpool (by have := size.isLt; omega)
    _ = _ := by simp
open _root_.P2M60f02c0e renaming h42 → _p2mH42
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h40 {Pool : Type*} [Fintype Pool] [DecidableEq Pool]
    (order : ℕ) (hpool : 1 ≤ Fintype.card Pool) :
    (_root_.CurrentAFT.FullResponseEnumeration.boundedSubsets Pool order).card ≤ (order + 1) * (Fintype.card Pool)^order := by
  exact (Finset.card_image_le).trans
    ((by simp only [Finset.card_univ] :
      (Finset.univ : Finset (SubsetWords Pool order)).card = Fintype.card (SubsetWords Pool order)).le.trans
      (_p2mH42 order hpool))
open _root_.P2M60f02c0e renaming h40 → _p2mH40
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h39 (security : ℕ) : Fintype.card (_root_.CurrentAFT.ActualBlockFock.BlockIndex security) = _root_.CurrentAFT.Parameters.bodySize security := by
  have hroom := _root_.CurrentAFT.ProposalPrimary.population_room security
  simp only [_root_.CurrentAFT.ActualBlockFock.BlockIndex, Fintype.card_sum, Fintype.card_fin, _root_.CurrentAFT.ActualBlockFock.centerCount]
  omega
open _root_.P2M60f02c0e renaming h39 → _p2mH39
end
open _root_.P2M60f02c0e renaming h39 → _p2mH39
open _root_.P2M60f02c0e renaming h40 → _p2mH40
open _root_.P2M60f02c0e renaming h41 → _p2mH41
open _root_.P2M60f02c0e renaming h42 → _p2mH42
end CurrentAFT.FullResponseEnumeration
open _root_.P2M60f02c0e renaming h39 → _p2mH39
open _root_.P2M60f02c0e renaming h40 → _p2mH40
open _root_.P2M60f02c0e renaming h41 → _p2mH41
open _root_.P2M60f02c0e renaming h42 → _p2mH42
end
open _root_.P2M60f02c0e renaming h39 → _p2mH39
open _root_.P2M60f02c0e renaming h40 → _p2mH40
open _root_.P2M60f02c0e renaming h41 → _p2mH41
open _root_.P2M60f02c0e renaming h42 → _p2mH42
namespace CurrentAFT.BinaryDiffuseCurrent
end CurrentAFT.BinaryDiffuseCurrent
namespace CurrentAFT.BinaryDiffuseCurrent.currentHeight
end CurrentAFT.BinaryDiffuseCurrent.currentHeight
namespace CurrentAFT.BinaryDiffuseProgram
end CurrentAFT.BinaryDiffuseProgram
namespace CurrentAFT.BinaryDiffuseProgram.sumHeight
end CurrentAFT.BinaryDiffuseProgram.sumHeight
namespace CurrentAFT.BinaryMarkedCurrent
end CurrentAFT.BinaryMarkedCurrent
namespace CurrentAFT.BinaryMarkedCurrent.currentHeight
end CurrentAFT.BinaryMarkedCurrent.currentHeight
namespace CurrentAFT.BinaryPairProgram
end CurrentAFT.BinaryPairProgram
namespace CurrentAFT.BinaryPairProgram.current
end CurrentAFT.BinaryPairProgram.current
namespace CurrentAFT.BinaryPairProgram.currentHeightPolynomial
end CurrentAFT.BinaryPairProgram.currentHeightPolynomial
namespace CurrentAFT.BinaryPairProgram.currentWorkPolynomial
end CurrentAFT.BinaryPairProgram.currentWorkPolynomial
namespace CurrentAFT.BinaryPairProgram.diffuseHeightPolynomial
end CurrentAFT.BinaryPairProgram.diffuseHeightPolynomial
namespace CurrentAFT.BinaryPairProgram.markedHeightPolynomial
end CurrentAFT.BinaryPairProgram.markedHeightPolynomial
namespace CurrentAFT.DiffuseProfiles.profile
end CurrentAFT.DiffuseProfiles.profile
namespace CurrentAFT.FirstResponse
end CurrentAFT.FirstResponse
namespace CurrentAFT.FirstResponse.response
end CurrentAFT.FirstResponse.response
namespace CurrentAFT.InwardAnchor.point
end CurrentAFT.InwardAnchor.point
namespace CurrentAFT.LocalPairProgram
end CurrentAFT.LocalPairProgram
namespace CurrentAFT.LocalPairProgram.current
end CurrentAFT.LocalPairProgram.current
namespace CurrentAFT.RationalProposalProgram
end CurrentAFT.RationalProposalProgram
namespace CurrentAFT.RationalProposalProgram.anchorKernel
end CurrentAFT.RationalProposalProgram.anchorKernel
namespace CurrentAFT.RationalProposalProgram.approximateAnchorLaw
end CurrentAFT.RationalProposalProgram.approximateAnchorLaw
namespace CurrentAFT.RationalProposalProgram.approximateAnchorPrimaryLaw
end CurrentAFT.RationalProposalProgram.approximateAnchorPrimaryLaw
namespace CurrentAFT.RationalProposalProgram.approximateCenterProfile
end CurrentAFT.RationalProposalProgram.approximateCenterProfile
namespace CurrentAFT.RationalProposalProgram.approximateSeedLaw
end CurrentAFT.RationalProposalProgram.approximateSeedLaw
namespace CurrentAFT.RationalProposalProgram.bodyKernel
end CurrentAFT.RationalProposalProgram.bodyKernel
namespace CurrentAFT.RationalProposalProgram.diffuseKernel
end CurrentAFT.RationalProposalProgram.diffuseKernel
namespace CurrentAFT.RationalProposalProgram.fairProfile
end CurrentAFT.RationalProposalProgram.fairProfile
namespace CurrentAFT.RationalProposalProgram.gaussianWeight
end CurrentAFT.RationalProposalProgram.gaussianWeight
namespace CurrentAFT.RationalProposalProgram.primary
end CurrentAFT.RationalProposalProgram.primary
namespace CurrentAFT.RationalProposalProgram.safeEntry
end CurrentAFT.RationalProposalProgram.safeEntry
namespace CurrentAFT.RationalProposalProgram.seedWeight
end CurrentAFT.RationalProposalProgram.seedWeight
section
namespace CurrentAFT.RationalFirstResponseProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles RationalProposalProgram
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
  DiffuseProfiles.actualProfile DiffuseProfiles.signProfile DiffuseProfiles.activation
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h111 (colors width output : ℕ) (positive : Bool) (blur source : ℤ) :
    |(_root_.CurrentAFT.RationalFirstResponseProgram.profileKernel colors width positive blur source output : ℝ)| ≤ 1 :=
  _p2mH0 _ _ _ _ _ _
open _root_.P2M60f02c0e renaming h111 → _p2mH111
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h112 (security : ℕ) (positive : Bool) (output : _root_.CurrentAFT.FirstHistogram.Palette security) :
    (_root_.CurrentAFT.DiffuseProfiles.actualSeedLaw security).expectation (fun seed =>
      (_root_.CurrentAFT.RationalFirstResponseProgram.profileKernel (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.Parameters.anchorWidth security) positive
        (_root_.CurrentAFT.DiffuseProfiles.actualBlur security seed) (_root_.CurrentAFT.DiffuseProfiles.actualSecond security seed) output.val : ℝ)) = _root_.CurrentAFT.DiffuseProfiles.actualProfile security positive output := by
  simp only [_root_.CurrentAFT.RationalFirstResponseProgram.profileKernel, _root_.AFT.V7Calibration.averagedSliceProgram_cast, _root_.CurrentAFT.DiffuseProfiles.actualProfile, _root_.CurrentAFT.DiffuseProfiles.profile,
    _root_.AFT.TrimmedSlice.mixedLaw, _root_.AFT.FiniteDist.expectation, _root_.CurrentAFT.DiffuseProfiles.intervalStart]
open _root_.P2M60f02c0e renaming h112 → _p2mH112
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h109 (security : ℕ) (positive : Bool) (output : _root_.CurrentAFT.FirstHistogram.Palette security) :
    |_root_.CurrentAFT.DiffuseProfiles.actualProfile security positive output| ≤ 1 := by
  rw [← _p2mH112]
  unfold _root_.AFT.FiniteDist.expectation
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ seed : _root_.CurrentAFT.DiffuseProfiles.ActualSeed security, (_root_.CurrentAFT.DiffuseProfiles.actualSeedLaw security).weight seed := by
      apply Finset.sum_le_sum
      intro seed _
      rw [abs_mul, abs_of_nonneg ((_root_.CurrentAFT.DiffuseProfiles.actualSeedLaw security).nonneg seed)]
      exact (mul_le_mul_of_nonneg_left (_p2mH111 _ _ _ _ _ _)
        ((_root_.CurrentAFT.DiffuseProfiles.actualSeedLaw security).nonneg seed)).trans_eq (mul_one _)
    _ = 1 := (_root_.CurrentAFT.DiffuseProfiles.actualSeedLaw security).sum_one
open _root_.P2M60f02c0e renaming h109 → _p2mH109
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h108 (security : ℕ) :
    1/(16*(_root_.CurrentAFT.Parameters.base security:ℝ)) ≤ _root_.CurrentAFT.RationalFirstResponseProgram.actualDenominator security := by
  have ha := _root_.CurrentAFT.FirstResponse.activation_lower_simple security
  have hd := _p2mH37 security
  change _root_.CurrentAFT.DiffuseProfiles.activation security/2 ≤ _root_.CurrentAFT.RationalFirstResponseProgram.actualDenominator security at hd
  have hal : 1/(8*(_root_.CurrentAFT.Parameters.base security:ℝ)) ≤ _root_.CurrentAFT.DiffuseProfiles.activation security/2 := by
    convert div_le_div_of_nonneg_right ha (by norm_num : (0:ℝ) ≤ 2) using 1 <;> first | rfl | ring
  apply le_trans _ (hal.trans hd)
  exact one_div_le_one_div_of_le (by have hb := _root_.CurrentAFT.FirstResponse.base_pos security; positivity) (by
    have hb := _root_.CurrentAFT.FirstResponse.base_pos security; nlinarith)
open _root_.P2M60f02c0e renaming h108 → _p2mH108
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h110 (security : ℕ) (color : _root_.CurrentAFT.FirstHistogram.Palette security) :
    |_root_.CurrentAFT.DiffuseProfiles.signProfile security color| ≤ 2 := by
  have ha := _root_.CurrentAFT.DiffuseProfiles.activation_pos security
  have hu := _root_.CurrentAFT.DiffuseProfiles.activation_le_half security
  unfold _root_.CurrentAFT.DiffuseProfiles.signProfile
  rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1-DiffuseProfiles.activation security)]
  have hgap : |_root_.CurrentAFT.DiffuseProfiles.actualProfile security true color - _root_.CurrentAFT.DiffuseProfiles.actualProfile security false color| ≤ 2 :=
    (abs_sub _ _).trans ((add_le_add (_p2mH109 security true color)
      (_p2mH109 security false color)).trans_eq (by norm_num))
  exact (mul_le_mul (by linarith : 1-DiffuseProfiles.activation security ≤ 1)
    hgap (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).trans_eq (by norm_num)
open _root_.P2M60f02c0e renaming h110 → _p2mH110
attribute [local irreducible] sufficientBits
end
open _root_.P2M60f02c0e renaming h108 → _p2mH108
open _root_.P2M60f02c0e renaming h109 → _p2mH109
open _root_.P2M60f02c0e renaming h110 → _p2mH110
open _root_.P2M60f02c0e renaming h111 → _p2mH111
open _root_.P2M60f02c0e renaming h112 → _p2mH112
end CurrentAFT.RationalFirstResponseProgram
open _root_.P2M60f02c0e renaming h108 → _p2mH108
open _root_.P2M60f02c0e renaming h109 → _p2mH109
open _root_.P2M60f02c0e renaming h110 → _p2mH110
open _root_.P2M60f02c0e renaming h111 → _p2mH111
open _root_.P2M60f02c0e renaming h112 → _p2mH112
end
open _root_.P2M60f02c0e renaming h108 → _p2mH108
open _root_.P2M60f02c0e renaming h109 → _p2mH109
open _root_.P2M60f02c0e renaming h110 → _p2mH110
open _root_.P2M60f02c0e renaming h111 → _p2mH111
open _root_.P2M60f02c0e renaming h112 → _p2mH112
namespace CurrentAFT.DiffuseProfiles.actualProfile
end CurrentAFT.DiffuseProfiles.actualProfile
namespace CurrentAFT.RationalFirstResponseProgram
end CurrentAFT.RationalFirstResponseProgram
namespace CurrentAFT.RationalFirstResponseProgram.functional
end CurrentAFT.RationalFirstResponseProgram.functional
namespace CurrentAFT.RationalFirstResponseProgram.inverse
end CurrentAFT.RationalFirstResponseProgram.inverse
namespace CurrentAFT.RationalFirstResponseProgram.precision_of_size
end CurrentAFT.RationalFirstResponseProgram.precision_of_size
namespace CurrentAFT.RationalFirstResponseProgram.profileKernel
end CurrentAFT.RationalFirstResponseProgram.profileKernel
namespace CurrentAFT.RationalFirstResponseProgram.sufficientBits
end CurrentAFT.RationalFirstResponseProgram.sufficientBits
namespace CurrentAFT.RationalFirstResponseProgram.sufficientBitsPolynomial
end CurrentAFT.RationalFirstResponseProgram.sufficientBitsPolynomial
section
namespace CurrentAFT.RationalPairedLiftProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles RationalProposalProgram
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference
section Generic
variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h160 (primary : _root_.AFT.FiniteDist Primary) (anchor : Primary → _root_.AFT.FiniteDist Body)
    (score : Primary → ℝ) (bound : ℝ) (hscore : ∀ color, |score color| ≤ bound) (output : Body) :
    |_root_.CurrentAFT.ControlCoordinates.anchorProfile primary anchor score output| ≤ bound := by
  unfold _root_.CurrentAFT.ControlCoordinates.anchorProfile
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ color, primary.weight color*bound := by
      apply Finset.sum_le_sum
      intro color _
      rw [abs_mul, abs_mul, abs_of_nonneg (primary.nonneg color), abs_of_nonneg ((anchor color).nonneg output)]
      exact (mul_le_mul (mul_le_mul_of_nonneg_left (hscore color) (primary.nonneg color))
        ((anchor color).atom_le_one output) ((anchor color).nonneg output)
        (mul_nonneg (primary.nonneg color) ((abs_nonneg _).trans (hscore color)))).trans_eq (mul_one _)
    _ = bound := by rw [← Finset.sum_mul, primary.sum_one, one_mul]
open _root_.P2M60f02c0e renaming h160 → _p2mH160
end Generic
open _root_.P2M60f02c0e renaming h160 → _p2mH160
end
open _root_.P2M60f02c0e renaming h160 → _p2mH160
end CurrentAFT.RationalPairedLiftProgram
open _root_.P2M60f02c0e renaming h160 → _p2mH160
end
open _root_.P2M60f02c0e renaming h160 → _p2mH160
namespace CurrentAFT.RationalPairedLiftProgram
end CurrentAFT.RationalPairedLiftProgram
namespace CurrentAFT.RationalPairedLiftProgram.anchorProfile
end CurrentAFT.RationalPairedLiftProgram.anchorProfile
namespace CurrentAFT.RationalPairedLiftProgram.current
end CurrentAFT.RationalPairedLiftProgram.current
section
namespace CurrentAFT.RationalRootMassProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles ProposalPrimary
  RationalProposalProgram LocalReferenceEnergy
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base primaryLaw centerLaw
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h176 (security : ℕ) (score : _root_.CurrentAFT.FirstHistogram.Palette security → ℝ)
    (primaryColor centerColor : _root_.CurrentAFT.FirstHistogram.Palette security) :
    _root_.CurrentAFT.RationalRootMassProgram.actualWeightedScore security score primaryColor centerColor =
      (_root_.CurrentAFT.ProposalPrimary.centerLaw security).weight centerColor * _root_.CurrentAFT.PairedResponse.pairedScore security score primaryColor centerColor := by
  unfold _root_.CurrentAFT.RationalRootMassProgram.actualWeightedScore _root_.CurrentAFT.PairedResponse.pairedScore _root_.CurrentAFT.PairedResponse.compensatorScore
  by_cases hzero : (_root_.CurrentAFT.ProposalPrimary.centerLaw security).weight centerColor = 0
  · rw [hzero, _root_.CurrentAFT.PairedResponse.centerLaw_zero_implies_anchorScore_zero security score centerColor hzero]
    ring
  · field_simp
open _root_.P2M60f02c0e renaming h176 → _p2mH176
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h173 (security : ℕ) (score : _root_.CurrentAFT.FirstHistogram.Palette security → ℝ)
    (output : _root_.CurrentAFT.FirstHistogram.Palette security) :
    _root_.CurrentAFT.PairedResponse.anchorWeightedScore security score output =
      _root_.CurrentAFT.ControlCoordinates.anchorProfile (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.InwardAnchor.smoothedAnchorLaw security) score output := by
  unfold _root_.CurrentAFT.PairedResponse.anchorWeightedScore _root_.CurrentAFT.ControlCoordinates.anchorProfile
  apply Finset.sum_congr rfl
  intro color _
  ring
open _root_.P2M60f02c0e renaming h173 → _p2mH173
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h172 (security : ℕ) (score : _root_.CurrentAFT.FirstHistogram.Palette security → ℝ)
    (bound : ℝ) (hb : 0 ≤ bound) (hscore : ∀ color, |score color| ≤ bound)
    (primaryColor centerColor : _root_.CurrentAFT.FirstHistogram.Palette security) :
    |_root_.CurrentAFT.RationalRootMassProgram.actualWeightedScore security score primaryColor centerColor| ≤ 2 * bound := by
  rw [_root_.CurrentAFT.RationalRootMassProgram.actualWeightedScore, _p2mH173]
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_of_nonneg ((_root_.CurrentAFT.ProposalPrimary.centerLaw security).nonneg centerColor),
    abs_mul, abs_of_pos (_root_.CurrentAFT.DiffuseProfiles.activation_pos security)]
  have hp := _p2mH160 (_root_.CurrentAFT.ProposalPrimary.primaryLaw security)
    (_root_.CurrentAFT.InwardAnchor.smoothedAnchorLaw security) score bound hscore centerColor
  have hfirst := mul_le_mul ((_root_.CurrentAFT.ProposalPrimary.centerLaw security).atom_le_one centerColor) (hscore primaryColor)
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hsecond := mul_le_mul (_root_.CurrentAFT.DiffuseProfiles.activation_le_half security) hp (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  nlinarith
open _root_.P2M60f02c0e renaming h172 → _p2mH172
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h171 (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : _root_.CurrentAFT.FirstHistogram.Scalar security) (centerColor : _root_.CurrentAFT.FirstHistogram.Palette security)
    (word : Fin 4 → _root_.CurrentAFT.FirstHistogram.Palette security) :
    |_root_.CurrentAFT.RationalRootMassProgram.actualRest security compensatorRoot attachmentRoot scalar centerColor word| ≤ 1 := by
  unfold _root_.CurrentAFT.RationalRootMassProgram.actualRest _root_.CurrentAFT.FirstHistogram.atom
  split_ifs
  · rw [mul_one, abs_of_nonneg ((_root_.CurrentAFT.LocalReferenceEnergy.attachmentAt security attachmentRoot scalar).nonneg _)]
    exact (_root_.CurrentAFT.LocalReferenceEnergy.attachmentAt security attachmentRoot scalar).atom_le_one _
  · norm_num
open _root_.P2M60f02c0e renaming h171 → _p2mH171
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h175 (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : _root_.CurrentAFT.FirstHistogram.Scalar security) (score : _root_.CurrentAFT.FirstHistogram.Palette security → ℝ)
    (word : Fin 4 → _root_.CurrentAFT.FirstHistogram.Palette security) :
    _root_.CurrentAFT.PairedReferenceEnergy.pairedMassAt security compensatorRoot attachmentRoot scalar score word =
      ∑ primaryColor, ∑ centerColor, (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight primaryColor *
        _root_.CurrentAFT.RationalRootMassProgram.actualWeightedScore security score primaryColor centerColor *
          (_root_.CurrentAFT.LocalReferenceEnergy.pairAt security primaryColor scalar).weight (word 1, word 2) *
            _root_.CurrentAFT.RationalRootMassProgram.actualRest security compensatorRoot attachmentRoot scalar centerColor word := by
  rw [_root_.CurrentAFT.PairedReferenceEnergy.pairedMassAt_control_sum]
  apply Finset.sum_congr rfl
  intro primaryColor _
  apply Finset.sum_congr rfl
  intro centerColor _
  rw [_p2mH176]
  unfold _root_.CurrentAFT.RationalRootMassProgram.actualRest _root_.CurrentAFT.FirstHistogram.atom
  split_ifs <;> ring
open _root_.P2M60f02c0e renaming h175 → _p2mH175
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h174 (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : _root_.CurrentAFT.FirstHistogram.Scalar security) (score : _root_.CurrentAFT.FirstHistogram.Palette security → ℝ)
    (bound : ℝ) (hb : 0 ≤ bound) (hscore : ∀ color, |score color| ≤ bound)
    (word : Fin 4 → _root_.CurrentAFT.FirstHistogram.Palette security) :
    |_root_.CurrentAFT.PairedReferenceEnergy.pairedMassAt security compensatorRoot attachmentRoot scalar score word| ≤
      (2 * (_root_.CurrentAFT.Parameters.modulus security : ℝ)^2) * bound := by
  rw [_p2mH175]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _primaryColor : _root_.CurrentAFT.FirstHistogram.Palette security,
        ∑ _centerColor : _root_.CurrentAFT.FirstHistogram.Palette security, 2 * bound := by
      apply Finset.sum_le_sum
      intro primaryColor _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro centerColor _
      simp only [abs_mul, abs_of_nonneg ((_root_.CurrentAFT.ProposalPrimary.primaryLaw security).nonneg _),
        abs_of_nonneg ((_root_.CurrentAFT.LocalReferenceEnergy.pairAt security primaryColor scalar).nonneg _)]
      have h := mul_le_mul
        (mul_le_mul (mul_le_mul ((_root_.CurrentAFT.ProposalPrimary.primaryLaw security).atom_le_one primaryColor)
          (_p2mH172 security score bound hb hscore primaryColor centerColor)
          (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))
          ((_root_.CurrentAFT.LocalReferenceEnergy.pairAt security primaryColor scalar).atom_le_one (word 1, word 2))
          ((_root_.CurrentAFT.LocalReferenceEnergy.pairAt security primaryColor scalar).nonneg (word 1, word 2))
          (by positivity : (0 : ℝ) ≤ 1 * (2 * bound)))
        (_p2mH171 security compensatorRoot attachmentRoot scalar centerColor word)
        (abs_nonneg _) (by positivity : (0 : ℝ) ≤ 1 * (2 * bound) * 1)
      simpa only [one_mul, mul_one] using h
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
open _root_.P2M60f02c0e renaming h174 → _p2mH174
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h177 (security : ℕ) (roots : _root_.CurrentAFT.RootTaggedSelected.RootPair security)
    (score : _root_.CurrentAFT.FirstHistogram.Palette security → ℝ) (word : Fin 4 → _root_.CurrentAFT.FirstHistogram.Palette security) :
    _root_.CurrentAFT.RootMassColumns.primaryMassAt security roots score word =
      ∑ scalar : _root_.CurrentAFT.FirstHistogram.Scalar security, (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).weight scalar *
        _root_.CurrentAFT.PairedReferenceEnergy.pairedMassAt security roots.1.val roots.2.val scalar score word := by
  simp only [_root_.CurrentAFT.RootMassColumns.primaryMassAt, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, _root_.CurrentAFT.PairedReferenceEnergy.pairedMassLinear_apply]
open _root_.P2M60f02c0e renaming h177 → _p2mH177
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h178 (security : ℕ) (roots : _root_.CurrentAFT.RootTaggedSelected.RootPair security)
    (score : _root_.CurrentAFT.FirstHistogram.Palette security → ℝ) (bound : ℝ) (hb : 0 ≤ bound)
    (hscore : ∀ color, |score color| ≤ bound) (word : Fin 4 → _root_.CurrentAFT.FirstHistogram.Palette security) :
    |_root_.CurrentAFT.RootMassColumns.primaryMassAt security roots score word| ≤
      (2 * (_root_.CurrentAFT.Parameters.modulus security : ℝ)^2) * bound := by
  rw [_p2mH177]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ scalar, (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).weight scalar * ((2 * (_root_.CurrentAFT.Parameters.modulus security : ℝ)^2) * bound) := by
      apply Finset.sum_le_sum
      intro scalar _
      rw [abs_mul, abs_of_nonneg ((_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).nonneg scalar)]
      exact mul_le_mul_of_nonneg_left (_p2mH174 security _ _ scalar score bound hb hscore word)
        ((_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).nonneg scalar)
    _ = _ := by rw [← Finset.sum_mul, (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).sum_one, one_mul]
open _root_.P2M60f02c0e renaming h178 → _p2mH178
end
open _root_.P2M60f02c0e renaming h171 → _p2mH171
open _root_.P2M60f02c0e renaming h172 → _p2mH172
open _root_.P2M60f02c0e renaming h173 → _p2mH173
open _root_.P2M60f02c0e renaming h174 → _p2mH174
open _root_.P2M60f02c0e renaming h175 → _p2mH175
open _root_.P2M60f02c0e renaming h176 → _p2mH176
open _root_.P2M60f02c0e renaming h177 → _p2mH177
open _root_.P2M60f02c0e renaming h178 → _p2mH178
end CurrentAFT.RationalRootMassProgram
open _root_.P2M60f02c0e renaming h171 → _p2mH171
open _root_.P2M60f02c0e renaming h172 → _p2mH172
open _root_.P2M60f02c0e renaming h173 → _p2mH173
open _root_.P2M60f02c0e renaming h174 → _p2mH174
open _root_.P2M60f02c0e renaming h175 → _p2mH175
open _root_.P2M60f02c0e renaming h176 → _p2mH176
open _root_.P2M60f02c0e renaming h177 → _p2mH177
open _root_.P2M60f02c0e renaming h178 → _p2mH178
end
open _root_.P2M60f02c0e renaming h171 → _p2mH171
open _root_.P2M60f02c0e renaming h172 → _p2mH172
open _root_.P2M60f02c0e renaming h173 → _p2mH173
open _root_.P2M60f02c0e renaming h174 → _p2mH174
open _root_.P2M60f02c0e renaming h175 → _p2mH175
open _root_.P2M60f02c0e renaming h176 → _p2mH176
open _root_.P2M60f02c0e renaming h177 → _p2mH177
open _root_.P2M60f02c0e renaming h178 → _p2mH178
namespace CurrentAFT.PrimaryTensorInverse
end CurrentAFT.PrimaryTensorInverse
namespace CurrentAFT.PrimaryTensorInverse.densityInverse
end CurrentAFT.PrimaryTensorInverse.densityInverse
namespace CurrentAFT.PrimaryTensorInverse.densityResponse
end CurrentAFT.PrimaryTensorInverse.densityResponse
namespace CurrentAFT.PrimaryTensorInverse.diagonal
end CurrentAFT.PrimaryTensorInverse.diagonal
namespace CurrentAFT.PrimaryTensorInverse.massDensity
end CurrentAFT.PrimaryTensorInverse.massDensity
namespace CurrentAFT.PrimaryTensorInverse.massLeading
end CurrentAFT.PrimaryTensorInverse.massLeading
namespace CurrentAFT.PrimaryTensorInverse.massLift
end CurrentAFT.PrimaryTensorInverse.massLift
section
namespace CurrentAFT.RationalDensityInverseProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles RationalProposalProgram
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h92 (security : ℕ) (profile : _root_.CurrentAFT.FirstHistogram.Palette security → ℝ)
    (bound : ℝ) (hb : 0 ≤ bound) (hprofile : ∀ color, |profile color| ≤ bound)
    (output : _root_.CurrentAFT.FirstHistogram.Palette security) :
    |(_root_.CurrentAFT.FirstResponse.responseEquiv security).symm profile output| ≤ _root_.CurrentAFT.RationalDensityInverseProgram.inverseBound security*bound := by
  have hfunctional : |_root_.AFT.signFunctional (_root_.CurrentAFT.FirstResponse.anchorSign security) profile| ≤
      (_root_.CurrentAFT.Parameters.modulus security:ℝ)*bound := by
    apply (_root_.AFT.signFunctional_abs_le_l1 _ _ (_root_.CurrentAFT.FirstResponse.anchorSign_abs_le_one security)).trans
    calc
      _ ≤ ∑ _color : _root_.CurrentAFT.FirstHistogram.Palette security, bound := Finset.sum_le_sum (fun color _ => hprofile color)
      _ = _ := by simp
  have hlo := _p2mH108 security
  have hb0 := _root_.CurrentAFT.FirstResponse.base_pos security
  have hpos : 0 < _root_.CurrentAFT.RationalFirstResponseProgram.actualDenominator security :=
    (by positivity : (0:ℝ)<1/(16*(Parameters.base security:ℝ))).trans_le hlo
  have hinv : (_root_.CurrentAFT.RationalFirstResponseProgram.actualDenominator security)⁻¹ ≤ 16*(_root_.CurrentAFT.Parameters.base security:ℝ) := by
    simpa only [one_div, inv_inv] using one_div_le_one_div_of_le
      (by positivity : (0:ℝ)<1/(16*(Parameters.base security:ℝ))) hlo
  rw [_p2mH38]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  calc
    _ ≤ |profile output| +
        |(_root_.CurrentAFT.RationalFirstResponseProgram.actualDenominator security)⁻¹ *
          _root_.AFT.signFunctional (_root_.CurrentAFT.FirstResponse.anchorSign security) profile * _root_.CurrentAFT.DiffuseProfiles.signProfile security output| := abs_sub _ _
    _ = |profile output| + (_root_.CurrentAFT.RationalFirstResponseProgram.actualDenominator security)⁻¹ *
        |_root_.AFT.signFunctional (_root_.CurrentAFT.FirstResponse.anchorSign security) profile| * |_root_.CurrentAFT.DiffuseProfiles.signProfile security output| := by
      simp only [abs_mul, abs_of_pos (inv_pos.mpr hpos)]
    _ ≤ bound+(16*(_root_.CurrentAFT.Parameters.base security:ℝ))*((_root_.CurrentAFT.Parameters.modulus security:ℝ)*bound)*2 :=
      add_le_add (hprofile output)
        (mul_le_mul (mul_le_mul hinv hfunctional (abs_nonneg _) (by positivity))
          (_p2mH110 security output) (abs_nonneg _) (by positivity))
    _ = _ := by unfold _root_.CurrentAFT.RationalDensityInverseProgram.inverseBound; ring
open _root_.P2M60f02c0e renaming h92 → _p2mH92
end
open _root_.P2M60f02c0e renaming h92 → _p2mH92
end CurrentAFT.RationalDensityInverseProgram
open _root_.P2M60f02c0e renaming h92 → _p2mH92
end
open _root_.P2M60f02c0e renaming h92 → _p2mH92
namespace CurrentAFT.RationalDensityInverseProgram
end CurrentAFT.RationalDensityInverseProgram
namespace CurrentAFT.RationalDensityInverseProgram.current
end CurrentAFT.RationalDensityInverseProgram.current
section
namespace CurrentAFT.RationalTensorInverseProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalTensorInverseProgram.classicalFinDecidableEq
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h192 (security : ℕ) : 0 ≤ _root_.CurrentAFT.RationalTensorInverseProgram.actualBound security := by
  unfold _root_.CurrentAFT.RationalTensorInverseProgram.actualBound _root_.CurrentAFT.RationalDensityInverseProgram.inverseBound
  positivity
open _root_.P2M60f02c0e renaming h192 → _p2mH192
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h195 (security : ℕ) : 0 ≤ _root_.CurrentAFT.RationalDensityInverseProgram.errorConstant security := by
  unfold _root_.CurrentAFT.RationalDensityInverseProgram.errorConstant _root_.CurrentAFT.RationalDensityInverseProgram.inverseBound
    _root_.CurrentAFT.RationalFirstResponseProgram.inverseErrorConstant
  positivity
open _root_.P2M60f02c0e renaming h195 → _p2mH195
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h193 (security : ℕ) (input : _root_.CurrentAFT.ActualControls.Palette security → ℝ) (bound : ℝ)
    (hb : 0 ≤ bound) (hinput : ∀ color, |input color| ≤ bound) (output : _root_.CurrentAFT.ActualControls.Palette security) :
    |_root_.CurrentAFT.PrimaryTensorInverse.densityInverse security input output| ≤ _root_.CurrentAFT.RationalTensorInverseProgram.actualBound security * bound := by
  let profile := fun color : _root_.CurrentAFT.ActualControls.Palette security => (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color * input color
  have hprofile (color : _root_.CurrentAFT.ActualControls.Palette security) : |profile color| ≤ bound := by
    dsimp only [profile]
    rw [abs_mul, abs_of_nonneg ((_root_.CurrentAFT.ProposalPrimary.primaryLaw security).nonneg color)]
    exact (mul_le_mul ((_root_.CurrentAFT.ProposalPrimary.primaryLaw security).atom_le_one color) (hinput color) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hnum := _p2mH92 security profile bound hb hprofile output
  have hb0 := _root_.CurrentAFT.FirstResponse.base_pos security
  have hq0 := _root_.CurrentAFT.FirstResponse.modulus_pos security
  have hp : 1 / (2 * (_root_.CurrentAFT.Parameters.modulus security : ℝ)) ≤ (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight output := by
    simpa only [_root_.CurrentAFT.ProposalPrimary.primaryLaw] using _root_.CurrentAFT.ProposalPrimary.primaryProfile_atom_lower security output
  have hden : 1 / (8 * (_root_.CurrentAFT.Parameters.base security : ℝ) * _root_.CurrentAFT.Parameters.modulus security) ≤
      _root_.CurrentAFT.DiffuseProfiles.activation security * (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight output := by
    calc
      _ = (1 / (4 * (_root_.CurrentAFT.Parameters.base security : ℝ))) * (1 / (2 * (_root_.CurrentAFT.Parameters.modulus security : ℝ))) := by ring
      _ ≤ _ := mul_le_mul (_root_.CurrentAFT.FirstResponse.activation_lower_simple security) hp (by positivity) (_root_.CurrentAFT.DiffuseProfiles.activation_pos security).le
  have hdenpos : 0 < _root_.CurrentAFT.DiffuseProfiles.activation security * (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight output :=
    mul_pos (_root_.CurrentAFT.DiffuseProfiles.activation_pos security) (_root_.CurrentAFT.ActualControls.primaryReference_positive security output)
  have hformula : _root_.CurrentAFT.PrimaryTensorInverse.densityInverse security input output =
      (_root_.CurrentAFT.FirstResponse.responseEquiv security).symm profile output /
        (_root_.CurrentAFT.DiffuseProfiles.activation security * (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight output) := by
    rw [_root_.CurrentAFT.PrimaryTensorInverse.densityInverse_apply]
    dsimp only [profile]
    ring
  rw [hformula, abs_div, abs_of_pos hdenpos]
  calc
    _ ≤ (_root_.CurrentAFT.RationalDensityInverseProgram.inverseBound security * bound) /
        (_root_.CurrentAFT.DiffuseProfiles.activation security * (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight output) :=
      div_le_div_of_nonneg_right hnum hdenpos.le
    _ ≤ (_root_.CurrentAFT.RationalDensityInverseProgram.inverseBound security * bound) /
        (1 / (8 * (_root_.CurrentAFT.Parameters.base security : ℝ) * _root_.CurrentAFT.Parameters.modulus security)) :=
      div_le_div_of_nonneg_left (by unfold _root_.CurrentAFT.RationalDensityInverseProgram.inverseBound; positivity)
        (by positivity) hden
    _ = _ := by unfold _root_.CurrentAFT.RationalTensorInverseProgram.actualBound; ring_nf; simp only [inv_inv]
open _root_.P2M60f02c0e renaming h193 → _p2mH193
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h196 (security : ℕ) : 1 ≤ _root_.CurrentAFT.RationalTensorInverseProgram.factorBound security := by
  unfold _root_.CurrentAFT.RationalTensorInverseProgram.factorBound
  linarith [_p2mH192 security, _p2mH195 security]
open _root_.P2M60f02c0e renaming h196 → _p2mH196
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h194 (security degree : ℕ)
    (first second : (Fin degree → _root_.CurrentAFT.ActualControls.Palette security) → ℝ) (error : ℝ)
    (he : 0 ≤ error) (hdiff : ∀ source, |first source - second source| ≤ error)
    (output : Fin degree → _root_.CurrentAFT.ActualControls.Palette security) :
    |_root_.CurrentAFT.PrimaryTensorInverse.tensorInverse security degree first output -
      _root_.CurrentAFT.PrimaryTensorInverse.tensorInverse security degree second output| ≤
        (_root_.CurrentAFT.Parameters.modulus security : ℝ)^degree * (_root_.CurrentAFT.RationalTensorInverseProgram.actualBound security)^degree * error := by
  change |_root_.AFT.TensorChannel.apply degree (fun _ => _root_.CurrentAFT.PrimaryTensorInverse.densityInverse security) first output -
    _root_.AFT.TensorChannel.apply degree (fun _ => _root_.CurrentAFT.PrimaryTensorInverse.densityInverse security) second output| ≤ _
  rw [_root_.AFT.TensorChannel.apply_formula_instance, _root_.AFT.TensorChannel.apply_formula_instance, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _source : Fin degree → _root_.CurrentAFT.ActualControls.Palette security, error * (_root_.CurrentAFT.RationalTensorInverseProgram.actualBound security)^degree := by
      apply Finset.sum_le_sum
      intro source _
      rw [← sub_mul, abs_mul]
      apply mul_le_mul (hdiff source) _ (abs_nonneg _) he
      rw [Finset.abs_prod]
      calc
        _ ≤ ∏ _index : Fin degree, _root_.CurrentAFT.RationalTensorInverseProgram.actualBound security :=
          Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun index _ => by
            simpa only [mul_one] using _p2mH193 security (Pi.single (source index) 1) 1
              (by norm_num) (fun color => by simp only [Pi.single_apply]; split_ifs <;> norm_num) (output index))
        _ = _ := by simp
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
open _root_.P2M60f02c0e renaming h194 → _p2mH194
end
open _root_.P2M60f02c0e renaming h192 → _p2mH192
open _root_.P2M60f02c0e renaming h193 → _p2mH193
open _root_.P2M60f02c0e renaming h194 → _p2mH194
open _root_.P2M60f02c0e renaming h195 → _p2mH195
open _root_.P2M60f02c0e renaming h196 → _p2mH196
end CurrentAFT.RationalTensorInverseProgram
open _root_.P2M60f02c0e renaming h192 → _p2mH192
open _root_.P2M60f02c0e renaming h193 → _p2mH193
open _root_.P2M60f02c0e renaming h194 → _p2mH194
open _root_.P2M60f02c0e renaming h195 → _p2mH195
open _root_.P2M60f02c0e renaming h196 → _p2mH196
end
open _root_.P2M60f02c0e renaming h192 → _p2mH192
open _root_.P2M60f02c0e renaming h193 → _p2mH193
open _root_.P2M60f02c0e renaming h194 → _p2mH194
open _root_.P2M60f02c0e renaming h195 → _p2mH195
open _root_.P2M60f02c0e renaming h196 → _p2mH196
namespace CurrentAFT.RationalProposalProgram.approximateCenterLaw
end CurrentAFT.RationalProposalProgram.approximateCenterLaw
namespace CurrentAFT.RationalRootMassProgram
end CurrentAFT.RationalRootMassProgram
namespace CurrentAFT.RationalRootMassProgram.actualWeightedScore
end CurrentAFT.RationalRootMassProgram.actualWeightedScore
namespace CurrentAFT.RationalRootMassProgram.primaryErrorConstant
end CurrentAFT.RationalRootMassProgram.primaryErrorConstant
namespace CurrentAFT.RationalRootMassProgram.weightedScore
end CurrentAFT.RationalRootMassProgram.weightedScore
namespace CurrentAFT.RationalTensorInverseProgram
end CurrentAFT.RationalTensorInverseProgram
namespace CurrentAFT.RationalTensorInverseProgram.entry
end CurrentAFT.RationalTensorInverseProgram.entry
namespace CurrentAFT.RootLegCoefficientFamily
end CurrentAFT.RootLegCoefficientFamily
namespace CurrentAFT.RootLegCoefficientFamily.orderedWordEquiv
end CurrentAFT.RootLegCoefficientFamily.orderedWordEquiv
namespace CurrentAFT.RootLegCoefficientFamily.selectedDensity
end CurrentAFT.RootLegCoefficientFamily.selectedDensity
namespace CurrentAFT.RootLegCoefficientFamily.selectedKernel
end CurrentAFT.RootLegCoefficientFamily.selectedKernel
section
namespace CurrentAFT.RationalLegCoefficientExtraction
open AFT DiffuseProfiles ProposalPrimary ActualControls
  ControlCoordinates ControlProduct
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalLegCoefficientExtraction.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalLegCoefficientExtraction.classicalSubtypeDecidableEq
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h123 (security degree : ℕ)
    (kernel : (Fin degree → _root_.CurrentAFT.ActualControls.Palette security) → ℝ) (permutation : Equiv.Perm (Fin degree))
    (output : Fin degree → _root_.CurrentAFT.ActualControls.Palette security) :
    _root_.CurrentAFT.PrimaryTensorInverse.tensorInverse security degree kernel (output ∘ permutation) =
      _root_.CurrentAFT.PrimaryTensorInverse.tensorInverse security degree (fun word => kernel (word ∘ permutation)) output := by
  change _root_.AFT.TensorChannel.apply degree (fun _ => _root_.CurrentAFT.PrimaryTensorInverse.densityInverse security) kernel (output ∘ permutation) =
    _root_.AFT.TensorChannel.apply degree (fun _ => _root_.CurrentAFT.PrimaryTensorInverse.densityInverse security) (fun word => kernel (word ∘ permutation)) output
  rw [_root_.AFT.TensorChannel.apply_formula_instance, _root_.AFT.TensorChannel.apply_formula_instance]
  rw [← (_root_.CurrentAFT.PrimaryTensorInverse.wordPermutation (Input := _root_.CurrentAFT.ActualControls.Palette security) degree permutation).sum_comp]
  apply Finset.sum_congr rfl
  intro source _
  congr 1
  exact Equiv.prod_comp permutation (fun index =>
    _root_.CurrentAFT.PrimaryTensorInverse.densityInverse security (Pi.single (source index) 1) (output index))
open _root_.P2M60f02c0e renaming h123 → _p2mH123
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h121 (security : ℕ) (mass : (Fin 3 → _root_.CurrentAFT.ActualControls.Palette security) → ℝ)
    (selected : Finset (Fin 3)) :
    _root_.CurrentAFT.RationalLegCoefficientExtraction.orderedDensity security mass selected = fun output =>
      _root_.CurrentAFT.RootLegCoefficientFamily.selectedDensity security selected.card mass selected (by simp)
        (output ∘ _root_.CurrentAFT.RationalLegCoefficientExtraction.orderPermutation selected) := by
  funext output
  unfold _root_.CurrentAFT.RationalLegCoefficientExtraction.orderedDensity _root_.CurrentAFT.RootLegCoefficientFamily.selectedDensity
  congr 1
  funext slot
  simp only [Function.comp_apply, _root_.CurrentAFT.RationalLegCoefficientExtraction.orderPermutation, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl
open _root_.P2M60f02c0e renaming h121 → _p2mH121
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h122 (security : ℕ) (mass : (Fin 3 → _root_.CurrentAFT.ActualControls.Palette security) → ℝ)
    (selected : Finset (Fin 3)) :
    (_root_.CurrentAFT.RootLegCoefficientFamily.selectedKernel security selected.card mass selected (by simp)).val =
      _root_.CurrentAFT.ControlProduct.symmetrize (fun (colors : Fin selected.card → _root_.CurrentAFT.ActualControls.Palette security) (_ : Fin 0 → _root_.CurrentAFT.ActualControls.SafePalette security) =>
        _root_.CurrentAFT.PrimaryTensorInverse.tensorInverse security selected.card (_root_.CurrentAFT.RationalLegCoefficientExtraction.orderedDensity security mass selected) colors) := by
  let raw : _root_.CurrentAFT.ControlCoordinates.DensityKernel (Primary := _root_.CurrentAFT.ActualControls.Palette security) (Body := _root_.CurrentAFT.ActualControls.SafePalette security) selected.card 0 :=
    fun colors _ => _root_.CurrentAFT.RootLegCoefficientFamily.normalizedSelectedDensity security selected.card mass selected (by simp) colors
  have hraw : (fun (colors : Fin selected.card → _root_.CurrentAFT.ActualControls.Palette security) (_ : Fin 0 → _root_.CurrentAFT.ActualControls.SafePalette security) =>
      _root_.CurrentAFT.PrimaryTensorInverse.tensorInverse security selected.card (_root_.CurrentAFT.RationalLegCoefficientExtraction.orderedDensity security mass selected) colors) =
      _root_.CurrentAFT.ControlProduct.reindexKernel (_root_.CurrentAFT.RationalLegCoefficientExtraction.orderPermutation selected) (Equiv.refl (Fin 0)) raw := by
    funext colors centers
    rw [_p2mH121, ← _p2mH123]
    rfl
  rw [hraw, _root_.CurrentAFT.ControlProduct.symmetrize_reindex_permutations]
  rfl
open _root_.P2M60f02c0e renaming h122 → _p2mH122
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h120 (security : ℕ) (source output : _root_.CurrentAFT.ActualControls.Palette security) :
    |(if source = output then (1 : ℝ) else 0) - 1 / (_root_.CurrentAFT.Parameters.modulus security : ℝ)| ≤ 1 := by
  have hq : (1 : ℝ) ≤ _root_.CurrentAFT.Parameters.modulus security := by
    exact_mod_cast (_root_.CurrentAFT.Parameters.modulus_spec security).2.two_le.trans' (by omega)
  have hl : 0 ≤ 1 / (_root_.CurrentAFT.Parameters.modulus security : ℝ) := by positivity
  have hu : 1 / (_root_.CurrentAFT.Parameters.modulus security : ℝ) ≤ 1 :=
    (div_le_iff₀ (_root_.CurrentAFT.FirstResponse.modulus_pos security)).mpr (by simpa using hq)
  split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
open _root_.P2M60f02c0e renaming h120 → _p2mH120
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h118 (security : ℕ) (source output : _root_.CurrentAFT.ActualControls.Palette security) :
    |_root_.AFT.MixedKernel.referenceAtom (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security) source output| ≤
      4 * (_root_.CurrentAFT.Parameters.modulus security : ℝ) := by
  have hq0 := _root_.CurrentAFT.FirstResponse.modulus_pos security
  have hp : 1 / (2 * (_root_.CurrentAFT.Parameters.modulus security : ℝ)) ≤ (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight output := by
    simpa only [_root_.CurrentAFT.ProposalPrimary.primaryLaw] using _root_.CurrentAFT.ProposalPrimary.primaryProfile_atom_lower security output
  rw [_root_.AFT.MixedKernel.referenceAtom_eq, _root_.CurrentAFT.LocalReferenceEnergy.uniformReference_weight, abs_div,
    abs_of_pos (_root_.CurrentAFT.ActualControls.primaryReference_positive security output)]
  calc
    _ ≤ 1 / (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight output :=
      div_le_div_of_nonneg_right (_p2mH120 security source output) (_root_.CurrentAFT.ActualControls.primaryReference_positive security output).le
    _ ≤ 1 / (1 / (2 * (_root_.CurrentAFT.Parameters.modulus security : ℝ))) :=
      one_div_le_one_div_of_le (by positivity) hp
    _ ≤ _ := by simp only [one_div, inv_inv]; linarith
open _root_.P2M60f02c0e renaming h118 → _p2mH118
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h119 (security : ℕ) (mass : (Fin 3 → _root_.CurrentAFT.ActualControls.Palette security) → ℝ)
    (selected : Finset (Fin 3)) (output : Fin selected.card → _root_.CurrentAFT.ActualControls.Palette security)
    (body : Fin 0 → _root_.CurrentAFT.ActualControls.SafePalette security) :
    (_root_.CurrentAFT.RootLegCoefficientFamily.selectedKernel security selected.card mass selected (by simp)).val output body =
      (_root_.AFT.FiniteDist.uniform (Equiv.Perm (Fin selected.card))).expectation (fun permutation =>
        _root_.CurrentAFT.PrimaryTensorInverse.tensorInverse security selected.card (_root_.CurrentAFT.RationalLegCoefficientExtraction.orderedDensity security mass selected)
          (output ∘ permutation)) := by
  rw [_p2mH122, _root_.CurrentAFT.ControlProduct.symmetrize_apply]
  simp only [Fintype.card_perm, Fintype.card_fin, Nat.factorial_zero, Nat.cast_one, inv_one, mul_one,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, one_mul]
  unfold _root_.AFT.FiniteDist.expectation
  simp only [_root_.AFT.FiniteDist.uniform_weight, ← Finset.mul_sum, Fintype.card_perm, Fintype.card_fin]
open _root_.P2M60f02c0e renaming h119 → _p2mH119
end
open _root_.P2M60f02c0e renaming h118 → _p2mH118
open _root_.P2M60f02c0e renaming h119 → _p2mH119
open _root_.P2M60f02c0e renaming h120 → _p2mH120
open _root_.P2M60f02c0e renaming h121 → _p2mH121
open _root_.P2M60f02c0e renaming h122 → _p2mH122
open _root_.P2M60f02c0e renaming h123 → _p2mH123
end CurrentAFT.RationalLegCoefficientExtraction
open _root_.P2M60f02c0e renaming h118 → _p2mH118
open _root_.P2M60f02c0e renaming h119 → _p2mH119
open _root_.P2M60f02c0e renaming h120 → _p2mH120
open _root_.P2M60f02c0e renaming h121 → _p2mH121
open _root_.P2M60f02c0e renaming h122 → _p2mH122
open _root_.P2M60f02c0e renaming h123 → _p2mH123
end
open _root_.P2M60f02c0e renaming h118 → _p2mH118
open _root_.P2M60f02c0e renaming h119 → _p2mH119
open _root_.P2M60f02c0e renaming h120 → _p2mH120
open _root_.P2M60f02c0e renaming h121 → _p2mH121
open _root_.P2M60f02c0e renaming h122 → _p2mH122
open _root_.P2M60f02c0e renaming h123 → _p2mH123
namespace CurrentAFT.CalibrationCoordinateError
end CurrentAFT.CalibrationCoordinateError
section
namespace CurrentAFT.RationalFamilyProductProgram
open AFT ControlCoordinates ControlProduct GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalFamilyProductProgram.productFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h96 {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body) {r s r' s' : ℕ}
    (first : _root_.CurrentAFT.ControlCoordinates.canonicalKernels primary body r s) (second : _root_.CurrentAFT.ControlCoordinates.canonicalKernels primary body r' s') :
    _root_.CurrentAFT.RationalFamilyProductProgram.homogeneous first.val second.val = (_root_.CurrentAFT.ControlProduct.homogeneousProduct primary body first second).val := by
  funext colors centers
  rw [_p2mH25]
  unfold _root_.CurrentAFT.RationalFamilyProductProgram.homogeneous _root_.CurrentAFT.RationalFamilyProductProgram.average
  apply congrArg (fun total : ℝ => ((r+r').factorial : ℝ)⁻¹ * ((s+s').factorial : ℝ)⁻¹ * total)
  apply Finset.sum_congr (by ext first; simp)
  intro firstOrder _
  apply Finset.sum_congr (by ext second; simp)
  intro secondOrder _
  rfl
open _root_.P2M60f02c0e renaming h96 → _p2mH96
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h100 {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body) (order : ℕ)
    (first second : _root_.CurrentAFT.GradedControlAlgebra.KernelFamily primary body order) :
    _root_.CurrentAFT.RationalFamilyProductProgram.product order (fun arity => (first arity).val) (fun arity => (second arity).val) =
      fun arity => (_root_.CurrentAFT.GradedControlAlgebra.familyProduct primary body order first second arity).val := by
  funext output colors centers
  simp only [_root_.CurrentAFT.RationalFamilyProductProgram.product, _root_.CurrentAFT.GradedControlAlgebra.familyProduct, Submodule.coe_sum, Finset.sum_apply]
  apply Finset.sum_congr (by ext left; simp)
  intro left _
  apply Finset.sum_congr (by ext right; simp)
  intro right _
  split_ifs with hmatch
  · rw [_p2mH96, _root_.CurrentAFT.GradedControlAlgebra.transportKernel_val]
    rfl
  · rfl
open _root_.P2M60f02c0e renaming h100 → _p2mH100
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h93 (r s : ℕ)
    (value : Equiv.Perm (Fin r) → Equiv.Perm (Fin s) → ℝ) (bound : ℝ)
    (hvalue : ∀ first second, |value first second| ≤ bound) : |_root_.CurrentAFT.RationalFamilyProductProgram.average r s value| ≤ bound := by
  have h := _p2mH21
    ((_root_.AFT.FiniteDist.uniform (Equiv.Perm (Fin r))).prod (_root_.AFT.FiniteDist.uniform (Equiv.Perm (Fin s))))
    (fun pair => value pair.1 pair.2) bound (fun pair => hvalue pair.1 pair.2)
  convert h using 1
  congr 1
  simp only [_root_.CurrentAFT.RationalFamilyProductProgram.average, _root_.AFT.FiniteDist.expectation, _root_.AFT.FiniteDist.prod_weight, _root_.AFT.FiniteDist.uniform_weight,
    Fintype.sum_prod_type, Fintype.card_perm, Fintype.card_fin, ← Finset.mul_sum]
  apply congrArg (fun total : ℝ => (r.factorial : ℝ)⁻¹ * (s.factorial : ℝ)⁻¹ * total)
  apply Finset.sum_congr (by ext first; simp)
  intro first _
  apply Finset.sum_congr (by ext second; simp)
  intro second _
  rfl
open _root_.P2M60f02c0e renaming h93 → _p2mH93
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h97 {Primary Body : Type*} {r s r' s' : ℕ}
    (first : _root_.CurrentAFT.RationalFamilyProductProgram.Kernel ℝ Primary Body r s) (second : _root_.CurrentAFT.RationalFamilyProductProgram.Kernel ℝ Primary Body r' s')
    (A B : ℝ) (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (ha : ∀ colors centers, |first colors centers| ≤ A)
    (hb : ∀ colors centers, |second colors centers| ≤ B)
    (colors : Fin (r+r') → Primary) (centers : Fin (s+s') → Body) :
    |_root_.CurrentAFT.RationalFamilyProductProgram.homogeneous first second colors centers| ≤ A*B := by
  apply _p2mH93
  intro p b
  unfold _root_.CurrentAFT.RationalFamilyProductProgram.tensor
  rw [abs_mul]
  exact mul_le_mul (ha _ _) (hb _ _) (abs_nonneg _) hA
open _root_.P2M60f02c0e renaming h97 → _p2mH97
end
open _root_.P2M60f02c0e renaming h93 → _p2mH93
open _root_.P2M60f02c0e renaming h96 → _p2mH96
open _root_.P2M60f02c0e renaming h97 → _p2mH97
open _root_.P2M60f02c0e renaming h100 → _p2mH100
end CurrentAFT.RationalFamilyProductProgram
open _root_.P2M60f02c0e renaming h93 → _p2mH93
open _root_.P2M60f02c0e renaming h96 → _p2mH96
open _root_.P2M60f02c0e renaming h97 → _p2mH97
open _root_.P2M60f02c0e renaming h100 → _p2mH100
end
open _root_.P2M60f02c0e renaming h93 → _p2mH93
open _root_.P2M60f02c0e renaming h96 → _p2mH96
open _root_.P2M60f02c0e renaming h97 → _p2mH97
open _root_.P2M60f02c0e renaming h100 → _p2mH100
namespace AFT.RationalNumerics.HeightBound
end AFT.RationalNumerics.HeightBound
namespace CurrentAFT.RationalFamilyProductProgram
end CurrentAFT.RationalFamilyProductProgram
namespace CurrentAFT.RationalFamilyProductProgram.average
end CurrentAFT.RationalFamilyProductProgram.average
namespace CurrentAFT.RationalFamilyProductProgram.homogeneous
end CurrentAFT.RationalFamilyProductProgram.homogeneous
namespace CurrentAFT.RationalFamilyProductProgram.product
end CurrentAFT.RationalFamilyProductProgram.product
namespace CurrentAFT.RationalFamilyProductProgram.realTable
end CurrentAFT.RationalFamilyProductProgram.realTable
namespace CurrentAFT.RationalFamilyProductProgram.tensor
end CurrentAFT.RationalFamilyProductProgram.tensor
section
namespace CurrentAFT.RationalFamilyProductProgram
open AFT RationalNumerics GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h101 {Primary Body : Type*} (order : ℕ)
    (first second : _root_.CurrentAFT.RationalFamilyProductProgram.Table ℝ Primary Body order) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ arity colors centers, |first arity colors centers| ≤ A)
    (hb : ∀ arity colors centers, |second arity colors centers| ≤ B)
    (output : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin output.val.1.val → Primary)
    (centers : Fin output.val.2.val → Body) :
    |_root_.CurrentAFT.RationalFamilyProductProgram.product order first second output colors centers| ≤
      (Fintype.card (_root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) : ℝ)^2 * (A*B) := by
  unfold _root_.CurrentAFT.RationalFamilyProductProgram.product
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _left : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order, ∑ _right : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order, (A*B) := by
      apply Finset.sum_le_sum
      intro left _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro right _
      split_ifs with hmatch
      · exact _p2mH97 _ _ A B hA hB (ha left) (hb right) _ _
      · simpa only [abs_zero] using mul_nonneg hA hB
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
open _root_.P2M60f02c0e renaming h101 → _p2mH101
end
open _root_.P2M60f02c0e renaming h101 → _p2mH101
end CurrentAFT.RationalFamilyProductProgram
open _root_.P2M60f02c0e renaming h101 → _p2mH101
end
open _root_.P2M60f02c0e renaming h101 → _p2mH101
namespace CurrentAFT.GradedInverse
end CurrentAFT.GradedInverse
namespace CurrentAFT.GradedInverse.backgroundInverse
end CurrentAFT.GradedInverse.backgroundInverse
section
namespace CurrentAFT.RationalFamilyProductProgram
open AFT ControlCoordinates ControlProduct GradedControlAlgebra GradedInverse
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalFamilyProductProgram.powerFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h104 {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body) (order : ℕ) :
    _root_.CurrentAFT.RationalFamilyProductProgram.unit (Scalar := ℝ) (Primary := Primary) (Body := Body) order =
      fun arity => ((1 : _root_.CurrentAFT.GradedControlAlgebra.KernelFamily primary body order) arity).val := by
  funext arity colors centers
  unfold _root_.CurrentAFT.RationalFamilyProductProgram.unit
  change _ = ((_root_.CurrentAFT.GradedControlAlgebra.familyUnit primary body order) arity).val colors centers
  by_cases heq : arity = _root_.CurrentAFT.GradedControlAlgebra.zeroArity order
  · subst arity
    simp only [_root_.CurrentAFT.GradedControlAlgebra.familyUnit, Pi.single_eq_same, if_true, _root_.CurrentAFT.ControlProduct.scalarUnit]
  · simp only [_root_.CurrentAFT.GradedControlAlgebra.familyUnit, Pi.single_eq_of_ne heq, heq, if_false, Submodule.coe_zero, Pi.zero_apply]
open _root_.P2M60f02c0e renaming h104 → _p2mH104
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h98 {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body) (order count : ℕ)
    (family : _root_.CurrentAFT.GradedControlAlgebra.KernelFamily primary body order) :
    _root_.CurrentAFT.RationalFamilyProductProgram.power order (fun arity => (family arity).val) count = fun arity => ((family^count) arity).val := by
  induction count with
  | zero => exact _p2mH104 primary body order
  | succ count ih =>
      rw [_root_.CurrentAFT.RationalFamilyProductProgram.power, ih, _p2mH100, pow_succ]
      rfl
open _root_.P2M60f02c0e renaming h98 → _p2mH98
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h102 {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body) (order : ℕ)
    (family : _root_.CurrentAFT.GradedControlAlgebra.KernelFamily primary body order) :
    _root_.CurrentAFT.RationalFamilyProductProgram.reciprocal order (fun arity => (family arity).val) =
      fun arity => (_root_.CurrentAFT.GradedInverse.backgroundInverse primary body order family arity).val := by
  have hsub : _root_.CurrentAFT.RationalFamilyProductProgram.unit order - (fun arity => (family arity).val) =
      fun arity => ((1 - family : _root_.CurrentAFT.GradedControlAlgebra.KernelFamily primary body order) arity).val := by
    rw [_p2mH104 primary body order]
    rfl
  funext arity colors centers
  simp only [_root_.CurrentAFT.RationalFamilyProductProgram.reciprocal, hsub, _p2mH98, _root_.CurrentAFT.GradedInverse.backgroundInverse, Finset.sum_apply, Submodule.coe_sum]
open _root_.P2M60f02c0e renaming h102 → _p2mH102
end
open _root_.P2M60f02c0e renaming h98 → _p2mH98
open _root_.P2M60f02c0e renaming h102 → _p2mH102
open _root_.P2M60f02c0e renaming h104 → _p2mH104
end CurrentAFT.RationalFamilyProductProgram
open _root_.P2M60f02c0e renaming h98 → _p2mH98
open _root_.P2M60f02c0e renaming h102 → _p2mH102
open _root_.P2M60f02c0e renaming h104 → _p2mH104
end
open _root_.P2M60f02c0e renaming h98 → _p2mH98
open _root_.P2M60f02c0e renaming h102 → _p2mH102
open _root_.P2M60f02c0e renaming h104 → _p2mH104
namespace CurrentAFT.RationalFamilyProductProgram.binomial
end CurrentAFT.RationalFamilyProductProgram.binomial
namespace CurrentAFT.RationalFamilyProductProgram.power
end CurrentAFT.RationalFamilyProductProgram.power
namespace CurrentAFT.RationalFamilyProductProgram.power.match_1
end CurrentAFT.RationalFamilyProductProgram.power.match_1
namespace CurrentAFT.RationalFamilyProductProgram.reciprocal
end CurrentAFT.RationalFamilyProductProgram.reciprocal
namespace CurrentAFT.RationalFamilyProductProgram.unit
end CurrentAFT.RationalFamilyProductProgram.unit
namespace CurrentAFT.RationalLegCoefficientExtraction
end CurrentAFT.RationalLegCoefficientExtraction
namespace CurrentAFT.RationalLegCoefficientExtraction.orderPermutation
end CurrentAFT.RationalLegCoefficientExtraction.orderPermutation
namespace CurrentAFT.RationalLegCoefficientExtraction.selectedKernel
end CurrentAFT.RationalLegCoefficientExtraction.selectedKernel
namespace CurrentAFT.RootLegCoefficientFamily.higherFamily
end CurrentAFT.RootLegCoefficientFamily.higherFamily
namespace CurrentAFT.RootLegCoefficientLinear
end CurrentAFT.RootLegCoefficientLinear
namespace CurrentAFT.RootLegCoefficientLinear.higherFamilyLinear
end CurrentAFT.RootLegCoefficientLinear.higherFamilyLinear
namespace CurrentAFT.RootLegCoefficientLinear.rootHigherLinear
end CurrentAFT.RootLegCoefficientLinear.rootHigherLinear
namespace CurrentAFT.RootLegCoefficientLinear.selectedFamilyLinear
end CurrentAFT.RootLegCoefficientLinear.selectedFamilyLinear
namespace CurrentAFT.RootLegNormalized
end CurrentAFT.RootLegNormalized
namespace CurrentAFT.RootLegNormalized.positiveFamily
end CurrentAFT.RootLegNormalized.positiveFamily
section
namespace CurrentAFT.RationalLegFamilyTable
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalLegFamilyTable.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalLegFamilyTable.classicalSubtypeDecidableEq
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h124 (security order : ℕ) (mass : (Fin 3 → _root_.CurrentAFT.ActualControls.Palette security) → ℝ)
    (selected : Finset (Fin 3)) (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order)
    (colors : Fin arity.val.1.val → _root_.CurrentAFT.ActualControls.Palette security) (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    _root_.CurrentAFT.RationalLegFamilyTable.insertSelected order selected
      (fun word => (_root_.CurrentAFT.RootLegCoefficientFamily.selectedKernel security selected.card mass selected (by simp)).val word Fin.elim0)
        arity colors centers =
      (_root_.CurrentAFT.RootLegCoefficientFamily.selectedFamily security order mass selected arity).val colors centers := by
  unfold _root_.CurrentAFT.RationalLegFamilyTable.insertSelected _root_.CurrentAFT.RootLegCoefficientFamily.selectedFamily
  by_cases hdegree : selected.card ≤ order
  · rw [dif_pos hdegree]
    by_cases hmatch : selected.card = arity.val.1.val ∧ 0 = arity.val.2.val
    · have harity : arity = _root_.CurrentAFT.RootLegCoefficientFamily.selectedArity order selected hdegree := by
        apply Subtype.ext
        apply Prod.ext
        · apply Fin.ext
          exact hmatch.1.symm
        · apply Fin.ext
          exact hmatch.2.symm
      subst arity
      rw [dif_pos hmatch, Pi.single_eq_same]
      have hcenters : centers = (Fin.elim0 : Fin 0 → _root_.CurrentAFT.ActualControls.SafePalette security) :=
        @Subsingleton.elim (Fin 0 → _root_.CurrentAFT.ActualControls.SafePalette security) inferInstance centers Fin.elim0
      rw [hcenters]
      rfl
    · have harity : arity ≠ _root_.CurrentAFT.RootLegCoefficientFamily.selectedArity order selected hdegree := by
        intro hequal
        apply hmatch
        subst arity
        exact ⟨rfl, rfl⟩
      rw [dif_neg hmatch]
      have hzero := Pi.single_eq_of_ne
        (M := fun point : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order =>
          _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) point.val.1.val point.val.2.val) harity
        (_root_.CurrentAFT.RootLegCoefficientFamily.selectedKernel security selected.card mass selected (by simp))
      rw [hzero]
      rfl
  · rw [dif_neg hdegree]
    have hmatch : ¬(selected.card = arity.val.1.val ∧ 0 = arity.val.2.val) := by
      intro h
      have hbound := arity.property
      omega
    rw [dif_neg hmatch]
    rfl
open _root_.P2M60f02c0e renaming h124 → _p2mH124
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h125 (security degree : ℕ) (massBound massError : ℝ)
    (hbound : 0 ≤ massBound) (herror : 0 ≤ massError) :
    0 ≤ _root_.CurrentAFT.RationalLegCoefficientExtraction.normalizedError security degree massBound massError := by
  unfold _root_.CurrentAFT.RationalLegCoefficientExtraction.normalizedError _root_.CurrentAFT.RationalLegCoefficientExtraction.extractionBound
    _root_.CurrentAFT.RationalLegCoefficientExtraction.extractionError _root_.CurrentAFT.RationalLegCoefficientExtraction.atomErrorConstant
    _root_.CurrentAFT.RationalTensorInverseProgram.tensorErrorConstant _root_.CurrentAFT.RationalRootMassProgram.primaryErrorConstant
  positivity [_p2mH192 security,
    _p2mH195 security, _p2mH196 security]
open _root_.P2M60f02c0e renaming h125 → _p2mH125
end
open _root_.P2M60f02c0e renaming h124 → _p2mH124
open _root_.P2M60f02c0e renaming h125 → _p2mH125
end CurrentAFT.RationalLegFamilyTable
open _root_.P2M60f02c0e renaming h124 → _p2mH124
open _root_.P2M60f02c0e renaming h125 → _p2mH125
end
open _root_.P2M60f02c0e renaming h124 → _p2mH124
open _root_.P2M60f02c0e renaming h125 → _p2mH125
namespace CurrentAFT.RationalLegFamilyTable
end CurrentAFT.RationalLegFamilyTable
namespace CurrentAFT.RationalLegFamilyTable.positive
end CurrentAFT.RationalLegFamilyTable.positive
section
namespace CurrentAFT.LegCoefficientPointBounds
open AFT DiffuseProfiles ProposalPrimary ActualControls CoefficientHilbert
  ControlCoordinates GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.LegCoefficientPointBounds.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.LegCoefficientPointBounds.classicalSubtypeDecidableEq
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h56 (security : ℕ) (mass : (Fin 3 → _root_.CurrentAFT.ActualControls.Palette security) → ℝ)
    (selected : Finset (Fin 3)) (bound : ℝ) (hb : 0 ≤ bound) (hmass : ∀ word, |mass word| ≤ bound)
    (output : Fin selected.card → _root_.CurrentAFT.ActualControls.Palette security) :
    |_root_.CurrentAFT.RationalLegCoefficientExtraction.orderedDensity security mass selected output| ≤
      (_root_.CurrentAFT.Parameters.modulus security : ℝ)^3 * bound * (4 * (_root_.CurrentAFT.Parameters.modulus security : ℝ))^selected.card := by
  unfold _root_.CurrentAFT.RationalLegCoefficientExtraction.orderedDensity _root_.AFT.LocalTensors.referenceRestrictedComponent
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _word : Fin 3 → _root_.CurrentAFT.ActualControls.Palette security, bound * (4 * (_root_.CurrentAFT.Parameters.modulus security : ℝ))^selected.card := by
      apply Finset.sum_le_sum
      intro word _
      rw [abs_mul, Finset.abs_prod]
      apply mul_le_mul (hmass word) _ (Finset.prod_nonneg fun _ _ => abs_nonneg _) hb
      calc
        _ ≤ ∏ _slot : selected, 4 * (_root_.CurrentAFT.Parameters.modulus security : ℝ) :=
          Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun slot _ => _p2mH118 security _ _)
        _ = _ := by simp
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
open _root_.P2M60f02c0e renaming h56 → _p2mH56
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h62 (security degree : ℕ) (profile : (Fin degree → _root_.CurrentAFT.ActualControls.Palette security) → ℝ)
    (bound : ℝ) (hb : 0 ≤ bound) (hprofile : ∀ word, |profile word| ≤ bound)
    (output : Fin degree → _root_.CurrentAFT.ActualControls.Palette security) :
    |_root_.CurrentAFT.PrimaryTensorInverse.tensorInverse security degree profile output| ≤
      (_root_.CurrentAFT.Parameters.modulus security : ℝ)^degree * (_root_.CurrentAFT.RationalTensorInverseProgram.actualBound security)^degree * bound := by
  have h := _p2mH194 security degree profile 0 bound hb
    (fun word => by simpa only [Pi.zero_apply, sub_zero] using hprofile word) output
  simpa only [map_zero, Pi.zero_apply, sub_zero] using h
open _root_.P2M60f02c0e renaming h62 → _p2mH62
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h59 (security : ℕ) (mass : (Fin 3 → _root_.CurrentAFT.ActualControls.Palette security) → ℝ)
    (selected : Finset (Fin 3)) (bound : ℝ) (hb : 0 ≤ bound) (hmass : ∀ word, |mass word| ≤ bound)
    (output : Fin selected.card → _root_.CurrentAFT.ActualControls.Palette security) (centers : Fin 0 → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |(_root_.CurrentAFT.RootLegCoefficientFamily.selectedKernel security selected.card mass selected (by simp)).val output centers| ≤
      (_root_.CurrentAFT.Parameters.modulus security : ℝ)^selected.card * (_root_.CurrentAFT.RationalTensorInverseProgram.actualBound security)^selected.card *
        ((_root_.CurrentAFT.Parameters.modulus security : ℝ)^3 * bound * (4 * (_root_.CurrentAFT.Parameters.modulus security : ℝ))^selected.card) := by
  rw [_p2mH119]
  apply _p2mH21
  intro permutation
  exact _p2mH62 security selected.card _ _ (by positivity) (_p2mH56 security mass selected bound hb hmass)
    (output ∘ permutation)
open _root_.P2M60f02c0e renaming h59 → _p2mH59
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h58 (security : ℕ) (bound : ℝ) (hb : 0 ≤ bound) : 0 ≤ _root_.CurrentAFT.LegCoefficientPointBounds.selectedBound security bound := by
  unfold _root_.CurrentAFT.LegCoefficientPointBounds.selectedBound
  positivity [_p2mH192 security]
open _root_.P2M60f02c0e renaming h58 → _p2mH58
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h60 (security : ℕ) (mass : (Fin 3 → _root_.CurrentAFT.ActualControls.Palette security) → ℝ)
    (selected : Finset (Fin 3)) (bound : ℝ) (hb : 0 ≤ bound) (hmass : ∀ word, |mass word| ≤ bound)
    (output : Fin selected.card → _root_.CurrentAFT.ActualControls.Palette security) (centers : Fin 0 → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |(_root_.CurrentAFT.RootLegCoefficientFamily.selectedKernel security selected.card mass selected (by simp)).val output centers| ≤
      _root_.CurrentAFT.LegCoefficientPointBounds.selectedBound security bound := by
  have hcard : selected.card ≤ 3 := (Finset.card_le_card (Finset.subset_univ selected)).trans_eq (by simp)
  have hq : (1 : ℝ) ≤ _root_.CurrentAFT.Parameters.modulus security := by
    exact_mod_cast (_root_.CurrentAFT.Parameters.modulus_spec security).2.two_le.trans' (by omega)
  have hM := _p2mH192 security
  have hqpow := pow_le_pow_right₀ hq hcard
  have hfour : (1 : ℝ) ≤ 4 * (_root_.CurrentAFT.Parameters.modulus security : ℝ) := by linarith
  have hfourpow := pow_le_pow_right₀ hfour hcard
  have hMpow : (_root_.CurrentAFT.RationalTensorInverseProgram.actualBound security)^selected.card ≤
      (1 + _root_.CurrentAFT.RationalTensorInverseProgram.actualBound security)^3 :=
    (pow_le_pow_left₀ hM (show _root_.CurrentAFT.RationalTensorInverseProgram.actualBound security ≤
        1 + _root_.CurrentAFT.RationalTensorInverseProgram.actualBound security by linarith) selected.card).trans
      (pow_le_pow_right₀ (by linarith) hcard)
  apply (_p2mH59 security mass selected bound hb hmass output centers).trans
  exact mul_le_mul (mul_le_mul hqpow hMpow (pow_nonneg hM _) (by positivity))
    (mul_le_mul_of_nonneg_left hfourpow (by positivity)) (by positivity) (by positivity)
open _root_.P2M60f02c0e renaming h60 → _p2mH60
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h55 (security order : ℕ) (mass : (Fin 3 → _root_.CurrentAFT.ActualControls.Palette security) → ℝ)
    (selected : Finset (Fin 3)) (bound : ℝ) (hb : 0 ≤ bound) (hmass : ∀ word, |mass word| ≤ bound)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.ActualControls.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |(_root_.CurrentAFT.RootLegCoefficientFamily.selectedFamily security order mass selected arity).val colors centers| ≤ _root_.CurrentAFT.LegCoefficientPointBounds.selectedBound security bound := by
  rw [← _p2mH124 security order mass selected arity colors centers]
  unfold _root_.CurrentAFT.RationalLegFamilyTable.insertSelected
  split_ifs with hmatch
  · exact _p2mH60 security mass selected bound hb hmass (colors ∘ finCongr hmatch.1) Fin.elim0
  · simpa only [abs_zero] using _p2mH58 security bound hb
open _root_.P2M60f02c0e renaming h55 → _p2mH55
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h61 (security order : ℕ) (mass : (Fin 3 → _root_.CurrentAFT.ActualControls.Palette security) → ℝ)
    (selectedSets : Finset (Finset (Fin 3))) (bound : ℝ) (hb : 0 ≤ bound) (hmass : ∀ word, |mass word| ≤ bound)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.ActualControls.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |∑ selected ∈ selectedSets, (_root_.CurrentAFT.RootLegCoefficientFamily.selectedFamily security order mass selected arity).val colors centers| ≤
      8 * _root_.CurrentAFT.LegCoefficientPointBounds.selectedBound security bound := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _selected ∈ selectedSets, _root_.CurrentAFT.LegCoefficientPointBounds.selectedBound security bound :=
      Finset.sum_le_sum (fun selected _ => _p2mH55 security order mass selected bound hb hmass arity colors centers)
    _ ≤ _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (_p2mH58 security bound hb)
      apply Nat.cast_le.mpr
      exact (Finset.card_le_card (Finset.subset_univ selectedSets)).trans_eq (by norm_num)
open _root_.P2M60f02c0e renaming h61 → _p2mH61
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h54 (security order : ℕ) (mass : (Fin 3 → _root_.CurrentAFT.ActualControls.Palette security) → ℝ)
    (bound : ℝ) (hb : 0 ≤ bound) (hmass : ∀ word, |mass word| ≤ bound)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.ActualControls.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |(_root_.CurrentAFT.RootLegCoefficientLinear.higherFamilyLinear security order mass arity).val colors centers| ≤
      8 * _root_.CurrentAFT.LegCoefficientPointBounds.selectedBound security bound := by
  rw [_root_.CurrentAFT.RootLegCoefficientLinear.higherFamilyLinear_apply]
  simpa only [_root_.CurrentAFT.RootLegCoefficientFamily.higherFamily, Finset.sum_apply, Submodule.coe_sum] using
    _p2mH61 security order mass _ bound hb hmass arity colors centers
open _root_.P2M60f02c0e renaming h54 → _p2mH54
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h57 (security order : ℕ) (law : _root_.AFT.FiniteDist (Fin 3 → _root_.CurrentAFT.ActualControls.Palette security))
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.ActualControls.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |(_root_.CurrentAFT.RootLegNormalized.positiveFamily security order law arity).val colors centers| ≤
      1 + 8 * _root_.CurrentAFT.LegCoefficientPointBounds.selectedBound security 1 := by
  unfold _root_.CurrentAFT.RootLegNormalized.positiveFamily _root_.CurrentAFT.RootLegNormalized.completeFamily
  rw [law.sum_one, one_smul]
  simp only [Pi.add_apply, Submodule.coe_add, Finset.sum_apply, Submodule.coe_sum]
  have hu : |((1 : _root_.CurrentAFT.RootLegCoefficientFamily.Family security order) arity).val colors centers| ≤ 1 := by
    rw [← congrFun (congrFun (congrFun
      (_p2mH104 (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order) arity) colors) centers]
    unfold _root_.CurrentAFT.RationalFamilyProductProgram.unit
    split_ifs <;> norm_num
  exact (abs_add_le _ _).trans (add_le_add hu (_p2mH61 security order law.weight _ 1 (by norm_num)
    (fun word => by rw [abs_of_nonneg (law.nonneg word)]; exact law.atom_le_one word) arity colors centers))
open _root_.P2M60f02c0e renaming h57 → _p2mH57
end
open _root_.P2M60f02c0e renaming h54 → _p2mH54
open _root_.P2M60f02c0e renaming h55 → _p2mH55
open _root_.P2M60f02c0e renaming h56 → _p2mH56
open _root_.P2M60f02c0e renaming h57 → _p2mH57
open _root_.P2M60f02c0e renaming h58 → _p2mH58
open _root_.P2M60f02c0e renaming h59 → _p2mH59
open _root_.P2M60f02c0e renaming h60 → _p2mH60
open _root_.P2M60f02c0e renaming h61 → _p2mH61
open _root_.P2M60f02c0e renaming h62 → _p2mH62
end CurrentAFT.LegCoefficientPointBounds
open _root_.P2M60f02c0e renaming h54 → _p2mH54
open _root_.P2M60f02c0e renaming h55 → _p2mH55
open _root_.P2M60f02c0e renaming h56 → _p2mH56
open _root_.P2M60f02c0e renaming h57 → _p2mH57
open _root_.P2M60f02c0e renaming h58 → _p2mH58
open _root_.P2M60f02c0e renaming h59 → _p2mH59
open _root_.P2M60f02c0e renaming h60 → _p2mH60
open _root_.P2M60f02c0e renaming h61 → _p2mH61
open _root_.P2M60f02c0e renaming h62 → _p2mH62
end
open _root_.P2M60f02c0e renaming h54 → _p2mH54
open _root_.P2M60f02c0e renaming h55 → _p2mH55
open _root_.P2M60f02c0e renaming h56 → _p2mH56
open _root_.P2M60f02c0e renaming h57 → _p2mH57
open _root_.P2M60f02c0e renaming h58 → _p2mH58
open _root_.P2M60f02c0e renaming h59 → _p2mH59
open _root_.P2M60f02c0e renaming h60 → _p2mH60
open _root_.P2M60f02c0e renaming h61 → _p2mH61
open _root_.P2M60f02c0e renaming h62 → _p2mH62
namespace CurrentAFT.LocalCoefficientFamily
end CurrentAFT.LocalCoefficientFamily
namespace CurrentAFT.LocalCoefficientFamily.orderedWordEquiv
end CurrentAFT.LocalCoefficientFamily.orderedWordEquiv
namespace CurrentAFT.LocalCoefficientFamily.selectedDensity
end CurrentAFT.LocalCoefficientFamily.selectedDensity
namespace CurrentAFT.LocalCoefficientFamily.selectedKernel
end CurrentAFT.LocalCoefficientFamily.selectedKernel
namespace CurrentAFT.PrimaryTensorInverse.referenceWeight
end CurrentAFT.PrimaryTensorInverse.referenceWeight
section
namespace CurrentAFT.RationalCoefficientExtraction
open AFT DiffuseProfiles ProposalPrimary ActualControls
  ControlCoordinates ControlProduct
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalCoefficientExtraction.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalCoefficientExtraction.classicalSubtypeDecidableEq
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h91 (security degree : ℕ)
    (kernel : (Fin degree → _root_.CurrentAFT.ActualControls.Palette security) → ℝ) (permutation : Equiv.Perm (Fin degree))
    (output : Fin degree → _root_.CurrentAFT.ActualControls.Palette security) :
    _root_.CurrentAFT.PrimaryTensorInverse.tensorInverse security degree kernel (output ∘ permutation) =
      _root_.CurrentAFT.PrimaryTensorInverse.tensorInverse security degree (fun word => kernel (word ∘ permutation)) output := by
  change _root_.AFT.TensorChannel.apply degree (fun _ => _root_.CurrentAFT.PrimaryTensorInverse.densityInverse security) kernel (output ∘ permutation) =
    _root_.AFT.TensorChannel.apply degree (fun _ => _root_.CurrentAFT.PrimaryTensorInverse.densityInverse security) (fun word => kernel (word ∘ permutation)) output
  rw [_root_.AFT.TensorChannel.apply_formula_instance, _root_.AFT.TensorChannel.apply_formula_instance]
  rw [← (_root_.CurrentAFT.PrimaryTensorInverse.wordPermutation (Input := _root_.CurrentAFT.ActualControls.Palette security) degree permutation).sum_comp]
  apply Finset.sum_congr rfl
  intro source _
  congr 1
  exact Equiv.prod_comp permutation (fun index =>
    _root_.CurrentAFT.PrimaryTensorInverse.densityInverse security (Pi.single (source index) 1) (output index))
open _root_.P2M60f02c0e renaming h91 → _p2mH91
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h89 (security : ℕ) (mass : (Fin 4 → _root_.CurrentAFT.ActualControls.Palette security) → ℝ)
    (selected : Finset (Fin 4)) :
    _root_.CurrentAFT.RationalCoefficientExtraction.orderedDensity security mass selected = fun output =>
      _root_.CurrentAFT.LocalCoefficientFamily.selectedDensity security selected.card mass selected (by simp)
        (output ∘ _root_.CurrentAFT.RationalCoefficientExtraction.orderPermutation selected) := by
  funext output
  unfold _root_.CurrentAFT.RationalCoefficientExtraction.orderedDensity _root_.CurrentAFT.LocalCoefficientFamily.selectedDensity
  congr 1
  funext slot
  simp only [Function.comp_apply, _root_.CurrentAFT.RationalCoefficientExtraction.orderPermutation, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl
open _root_.P2M60f02c0e renaming h89 → _p2mH89
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h90 (security : ℕ) (mass : (Fin 4 → _root_.CurrentAFT.ActualControls.Palette security) → ℝ)
    (selected : Finset (Fin 4)) :
    (_root_.CurrentAFT.LocalCoefficientFamily.selectedKernel security selected.card mass selected (by simp)).val =
      _root_.CurrentAFT.ControlProduct.symmetrize (fun (colors : Fin selected.card → _root_.CurrentAFT.ActualControls.Palette security) (_ : Fin 0 → _root_.CurrentAFT.ActualControls.SafePalette security) =>
        _root_.CurrentAFT.PrimaryTensorInverse.tensorInverse security selected.card (_root_.CurrentAFT.RationalCoefficientExtraction.orderedDensity security mass selected) colors) := by
  let raw : _root_.CurrentAFT.ControlCoordinates.DensityKernel (Primary := _root_.CurrentAFT.ActualControls.Palette security) (Body := _root_.CurrentAFT.ActualControls.SafePalette security) selected.card 0 :=
    fun colors _ => _root_.CurrentAFT.LocalCoefficientFamily.normalizedSelectedDensity security selected.card mass selected (by simp) colors
  have hraw : (fun (colors : Fin selected.card → _root_.CurrentAFT.ActualControls.Palette security) (_ : Fin 0 → _root_.CurrentAFT.ActualControls.SafePalette security) =>
      _root_.CurrentAFT.PrimaryTensorInverse.tensorInverse security selected.card (_root_.CurrentAFT.RationalCoefficientExtraction.orderedDensity security mass selected) colors) =
      _root_.CurrentAFT.ControlProduct.reindexKernel (_root_.CurrentAFT.RationalCoefficientExtraction.orderPermutation selected) (Equiv.refl (Fin 0)) raw := by
    funext colors centers
    rw [_p2mH89, ← _p2mH91]
    rfl
  rw [hraw, _root_.CurrentAFT.ControlProduct.symmetrize_reindex_permutations]
  rfl
open _root_.P2M60f02c0e renaming h90 → _p2mH90
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h88 (security : ℕ) (source output : _root_.CurrentAFT.ActualControls.Palette security) :
    |(if source = output then (1 : ℝ) else 0) - 1 / (_root_.CurrentAFT.Parameters.modulus security : ℝ)| ≤ 1 := by
  have hq : (1 : ℝ) ≤ _root_.CurrentAFT.Parameters.modulus security := by
    exact_mod_cast (_root_.CurrentAFT.Parameters.modulus_spec security).2.two_le.trans' (by omega)
  have hl : 0 ≤ 1 / (_root_.CurrentAFT.Parameters.modulus security : ℝ) := by positivity
  have hu : 1 / (_root_.CurrentAFT.Parameters.modulus security : ℝ) ≤ 1 :=
    (div_le_iff₀ (_root_.CurrentAFT.FirstResponse.modulus_pos security)).mpr (by simpa using hq)
  split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
open _root_.P2M60f02c0e renaming h88 → _p2mH88
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h86 (security : ℕ) (source output : _root_.CurrentAFT.ActualControls.Palette security) :
    |_root_.AFT.MixedKernel.referenceAtom (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security) source output| ≤
      4 * (_root_.CurrentAFT.Parameters.modulus security : ℝ) := by
  have hq0 := _root_.CurrentAFT.FirstResponse.modulus_pos security
  have hp : 1 / (2 * (_root_.CurrentAFT.Parameters.modulus security : ℝ)) ≤ (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight output := by
    simpa only [_root_.CurrentAFT.ProposalPrimary.primaryLaw] using _root_.CurrentAFT.ProposalPrimary.primaryProfile_atom_lower security output
  rw [_root_.AFT.MixedKernel.referenceAtom_eq, _root_.CurrentAFT.LocalReferenceEnergy.uniformReference_weight, abs_div,
    abs_of_pos (_root_.CurrentAFT.ActualControls.primaryReference_positive security output)]
  calc
    _ ≤ 1 / (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight output :=
      div_le_div_of_nonneg_right (_p2mH88 security source output) (_root_.CurrentAFT.ActualControls.primaryReference_positive security output).le
    _ ≤ 1 / (1 / (2 * (_root_.CurrentAFT.Parameters.modulus security : ℝ))) :=
      one_div_le_one_div_of_le (by positivity) hp
    _ ≤ _ := by simp only [one_div, inv_inv]; linarith
open _root_.P2M60f02c0e renaming h86 → _p2mH86
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h87 (security : ℕ) (mass : (Fin 4 → _root_.CurrentAFT.ActualControls.Palette security) → ℝ)
    (selected : Finset (Fin 4)) (output : Fin selected.card → _root_.CurrentAFT.ActualControls.Palette security)
    (body : Fin 0 → _root_.CurrentAFT.ActualControls.SafePalette security) :
    (_root_.CurrentAFT.LocalCoefficientFamily.selectedKernel security selected.card mass selected (by simp)).val output body =
      (_root_.AFT.FiniteDist.uniform (Equiv.Perm (Fin selected.card))).expectation (fun permutation =>
        _root_.CurrentAFT.PrimaryTensorInverse.tensorInverse security selected.card (_root_.CurrentAFT.RationalCoefficientExtraction.orderedDensity security mass selected)
          (output ∘ permutation)) := by
  rw [_p2mH90, _root_.CurrentAFT.ControlProduct.symmetrize_apply]
  simp only [Fintype.card_perm, Fintype.card_fin, Nat.factorial_zero, Nat.cast_one, inv_one, mul_one,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, one_mul]
  unfold _root_.AFT.FiniteDist.expectation
  simp only [_root_.AFT.FiniteDist.uniform_weight, ← Finset.mul_sum, Fintype.card_perm, Fintype.card_fin]
open _root_.P2M60f02c0e renaming h87 → _p2mH87
end
open _root_.P2M60f02c0e renaming h86 → _p2mH86
open _root_.P2M60f02c0e renaming h87 → _p2mH87
open _root_.P2M60f02c0e renaming h88 → _p2mH88
open _root_.P2M60f02c0e renaming h89 → _p2mH89
open _root_.P2M60f02c0e renaming h90 → _p2mH90
open _root_.P2M60f02c0e renaming h91 → _p2mH91
end CurrentAFT.RationalCoefficientExtraction
open _root_.P2M60f02c0e renaming h86 → _p2mH86
open _root_.P2M60f02c0e renaming h87 → _p2mH87
open _root_.P2M60f02c0e renaming h88 → _p2mH88
open _root_.P2M60f02c0e renaming h89 → _p2mH89
open _root_.P2M60f02c0e renaming h90 → _p2mH90
open _root_.P2M60f02c0e renaming h91 → _p2mH91
end
open _root_.P2M60f02c0e renaming h86 → _p2mH86
open _root_.P2M60f02c0e renaming h87 → _p2mH87
open _root_.P2M60f02c0e renaming h88 → _p2mH88
open _root_.P2M60f02c0e renaming h89 → _p2mH89
open _root_.P2M60f02c0e renaming h90 → _p2mH90
open _root_.P2M60f02c0e renaming h91 → _p2mH91
namespace CurrentAFT.RationalSelectedRootProgram
end CurrentAFT.RationalSelectedRootProgram
section
namespace CurrentAFT.RationalPrimaryColumnProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls CoefficientHilbert
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalPrimaryColumnProgram.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalPrimaryColumnProgram.classicalSubtypeDecidableEq
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h161 (security : ℕ) (source color : _root_.CurrentAFT.ActualControls.Palette security) :
    _root_.CurrentAFT.CoefficientHilbert.centerLinear (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (Pi.single source 1) color =
      (if color = source then (1 : ℝ) else 0) - (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight source := by
  change (Pi.single (M := fun _ : _root_.CurrentAFT.ActualControls.Palette security => ℝ) source 1) color -
    (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).expectation (Pi.single source 1) = _
  simp [Pi.single_apply, _root_.AFT.FiniteDist.expectation]
open _root_.P2M60f02c0e renaming h161 → _p2mH161
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h162 (security : ℕ) (source color : _root_.CurrentAFT.ActualControls.Palette security) :
    |_root_.CurrentAFT.CoefficientHilbert.centerLinear (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (Pi.single source 1) color| ≤ 1 := by
  rw [_p2mH161]
  have hlo := (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).nonneg source
  have hhi := (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).atom_le_one source
  split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
open _root_.P2M60f02c0e renaming h162 → _p2mH162
end
open _root_.P2M60f02c0e renaming h161 → _p2mH161
open _root_.P2M60f02c0e renaming h162 → _p2mH162
end CurrentAFT.RationalPrimaryColumnProgram
open _root_.P2M60f02c0e renaming h161 → _p2mH161
open _root_.P2M60f02c0e renaming h162 → _p2mH162
end
open _root_.P2M60f02c0e renaming h161 → _p2mH161
open _root_.P2M60f02c0e renaming h162 → _p2mH162
namespace CurrentAFT.RationalPrimaryColumnProgram
end CurrentAFT.RationalPrimaryColumnProgram
section
namespace CurrentAFT.RationalLocalFamilyProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls CoefficientHilbert
  ControlCoordinates GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalLocalFamilyProgram.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalLocalFamilyProgram.classicalSubtypeDecidableEq
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h129 (security order : ℕ) (mass : (Fin 4 → _root_.CurrentAFT.ActualControls.Palette security) → ℝ)
    (selected : Finset (Fin 4)) (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order)
    (colors : Fin arity.val.1.val → _root_.CurrentAFT.ActualControls.Palette security) (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    _root_.CurrentAFT.RationalLocalFamilyProgram.insertSelected order selected
      (fun word => (_root_.CurrentAFT.LocalCoefficientFamily.selectedKernel security selected.card mass selected (by simp)).val word Fin.elim0)
        arity colors centers =
      (_root_.CurrentAFT.LocalCoefficientFamily.selectedFamily security order mass selected arity).val colors centers := by
  unfold _root_.CurrentAFT.RationalLocalFamilyProgram.insertSelected _root_.CurrentAFT.LocalCoefficientFamily.selectedFamily
  by_cases hdegree : selected.card ≤ order
  · rw [dif_pos hdegree]
    by_cases hmatch : selected.card = arity.val.1.val ∧ 0 = arity.val.2.val
    · have harity : arity = _root_.CurrentAFT.LocalCoefficientFamily.selectedArity order selected hdegree := by
        apply Subtype.ext
        apply Prod.ext
        · apply Fin.ext
          exact hmatch.1.symm
        · apply Fin.ext
          exact hmatch.2.symm
      subst arity
      rw [dif_pos hmatch, Pi.single_eq_same]
      have hcenters : centers = (Fin.elim0 : Fin 0 → _root_.CurrentAFT.ActualControls.SafePalette security) :=
        @Subsingleton.elim (Fin 0 → _root_.CurrentAFT.ActualControls.SafePalette security) inferInstance centers Fin.elim0
      rw [hcenters]
      rfl
    · have harity : arity ≠ _root_.CurrentAFT.LocalCoefficientFamily.selectedArity order selected hdegree := by
        intro hequal
        apply hmatch
        subst arity
        exact ⟨rfl, rfl⟩
      rw [dif_neg hmatch]
      have hzero := Pi.single_eq_of_ne
        (M := fun point : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order =>
          _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) point.val.1.val point.val.2.val) harity
        (_root_.CurrentAFT.LocalCoefficientFamily.selectedKernel security selected.card mass selected (by simp))
      rw [hzero]
      rfl
  · rw [dif_neg hdegree]
    have hmatch : ¬(selected.card = arity.val.1.val ∧ 0 = arity.val.2.val) := by
      intro h
      have hbound := arity.property
      omega
    rw [dif_neg hmatch]
    rfl
open _root_.P2M60f02c0e renaming h129 → _p2mH129
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h128 (security order : ℕ) (mass : (Fin 4 → _root_.CurrentAFT.ActualControls.Palette security) → ℝ)
    (hmass : ∑ word, mass word = 0) (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order)
    (colors : Fin arity.val.1.val → _root_.CurrentAFT.ActualControls.Palette security) (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    (_root_.CurrentAFT.LocalRaisingLinear.completeFamilyLinear security order mass arity).val colors centers =
      ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).erase ∅,
        _root_.CurrentAFT.RationalLocalFamilyProgram.insertSelected order selected
          (fun word => (_root_.CurrentAFT.LocalCoefficientFamily.selectedKernel security selected.card mass selected (by simp)).val word Fin.elim0)
          arity colors centers := by
  change (_root_.CurrentAFT.NormalizedLocalPolynomial.completeFamily security order mass arity).val colors centers = _
  unfold _root_.CurrentAFT.NormalizedLocalPolynomial.completeFamily
  rw [hmass, zero_smul, zero_add]
  simp only [Finset.sum_apply, Submodule.coe_sum]
  apply Finset.sum_congr (by ext; simp)
  intro selected _
  exact (_p2mH129 security order mass selected arity colors centers).symm
open _root_.P2M60f02c0e renaming h128 → _p2mH128
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h130 (security : ℕ) (roots : _root_.CurrentAFT.RootTaggedSelected.RootPair security) (primaryColor : _root_.CurrentAFT.ActualControls.Palette security) :
    (∑ word, _root_.CurrentAFT.RootMassColumns.primaryMassAt security roots
      (_root_.CurrentAFT.CoefficientHilbert.centerLinear (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (Pi.single primaryColor 1)) word) = 0 := by
  simp only [_p2mH177]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro scalar _
  rw [← Finset.mul_sum, _root_.CurrentAFT.FixedPairedFirst.fixedMass_sum, _root_.CurrentAFT.CoefficientHilbert.center_mean, mul_zero, mul_zero]
open _root_.P2M60f02c0e renaming h130 → _p2mH130
end
open _root_.P2M60f02c0e renaming h128 → _p2mH128
open _root_.P2M60f02c0e renaming h129 → _p2mH129
open _root_.P2M60f02c0e renaming h130 → _p2mH130
end CurrentAFT.RationalLocalFamilyProgram
open _root_.P2M60f02c0e renaming h128 → _p2mH128
open _root_.P2M60f02c0e renaming h129 → _p2mH129
open _root_.P2M60f02c0e renaming h130 → _p2mH130
end
open _root_.P2M60f02c0e renaming h128 → _p2mH128
open _root_.P2M60f02c0e renaming h129 → _p2mH129
open _root_.P2M60f02c0e renaming h130 → _p2mH130
namespace CurrentAFT.RationalLocalFamilyProgram
end CurrentAFT.RationalLocalFamilyProgram
section
namespace CurrentAFT.LocalCoefficientPointBounds
open AFT DiffuseProfiles ProposalPrimary ActualControls CoefficientHilbert
  ControlCoordinates GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.LocalCoefficientPointBounds.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.LocalCoefficientPointBounds.classicalSubtypeDecidableEq
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h65 (security : ℕ) (mass : (Fin 4 → _root_.CurrentAFT.ActualControls.Palette security) → ℝ)
    (selected : Finset (Fin 4)) (bound : ℝ) (hb : 0 ≤ bound) (hmass : ∀ word, |mass word| ≤ bound)
    (output : Fin selected.card → _root_.CurrentAFT.ActualControls.Palette security) :
    |_root_.CurrentAFT.RationalCoefficientExtraction.orderedDensity security mass selected output| ≤
      (_root_.CurrentAFT.Parameters.modulus security : ℝ)^4 * bound * (4 * (_root_.CurrentAFT.Parameters.modulus security : ℝ))^selected.card := by
  unfold _root_.CurrentAFT.RationalCoefficientExtraction.orderedDensity _root_.AFT.LocalTensors.referenceRestrictedComponent
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _word : Fin 4 → _root_.CurrentAFT.ActualControls.Palette security, bound * (4 * (_root_.CurrentAFT.Parameters.modulus security : ℝ))^selected.card := by
      apply Finset.sum_le_sum
      intro word _
      rw [abs_mul, Finset.abs_prod]
      apply mul_le_mul (hmass word) _ (Finset.prod_nonneg fun _ _ => abs_nonneg _) hb
      calc
        _ ≤ ∏ _slot : selected, 4 * (_root_.CurrentAFT.Parameters.modulus security : ℝ) :=
          Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun slot _ => _p2mH86 security _ _)
        _ = _ := by simp
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
open _root_.P2M60f02c0e renaming h65 → _p2mH65
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h69 (security degree : ℕ) (profile : (Fin degree → _root_.CurrentAFT.ActualControls.Palette security) → ℝ)
    (bound : ℝ) (hb : 0 ≤ bound) (hprofile : ∀ word, |profile word| ≤ bound)
    (output : Fin degree → _root_.CurrentAFT.ActualControls.Palette security) :
    |_root_.CurrentAFT.PrimaryTensorInverse.tensorInverse security degree profile output| ≤
      (_root_.CurrentAFT.Parameters.modulus security : ℝ)^degree * (_root_.CurrentAFT.RationalTensorInverseProgram.actualBound security)^degree * bound := by
  have h := _p2mH194 security degree profile 0 bound hb
    (fun word => by simpa only [Pi.zero_apply, sub_zero] using hprofile word) output
  simpa only [map_zero, Pi.zero_apply, sub_zero] using h
open _root_.P2M60f02c0e renaming h69 → _p2mH69
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h67 (security : ℕ) (mass : (Fin 4 → _root_.CurrentAFT.ActualControls.Palette security) → ℝ)
    (selected : Finset (Fin 4)) (bound : ℝ) (hb : 0 ≤ bound) (hmass : ∀ word, |mass word| ≤ bound)
    (output : Fin selected.card → _root_.CurrentAFT.ActualControls.Palette security) (centers : Fin 0 → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |(_root_.CurrentAFT.LocalCoefficientFamily.selectedKernel security selected.card mass selected (by simp)).val output centers| ≤
      (_root_.CurrentAFT.Parameters.modulus security : ℝ)^selected.card * (_root_.CurrentAFT.RationalTensorInverseProgram.actualBound security)^selected.card *
        ((_root_.CurrentAFT.Parameters.modulus security : ℝ)^4 * bound * (4 * (_root_.CurrentAFT.Parameters.modulus security : ℝ))^selected.card) := by
  rw [_p2mH87]
  apply _p2mH21
  intro permutation
  exact _p2mH69 security selected.card _ _ (by positivity) (_p2mH65 security mass selected bound hb hmass)
    (output ∘ permutation)
open _root_.P2M60f02c0e renaming h67 → _p2mH67
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h66 (security : ℕ) (bound : ℝ) (hb : 0 ≤ bound) : 0 ≤ _root_.CurrentAFT.LocalCoefficientPointBounds.selectedBound security bound := by
  unfold _root_.CurrentAFT.LocalCoefficientPointBounds.selectedBound
  positivity [_p2mH192 security]
open _root_.P2M60f02c0e renaming h66 → _p2mH66
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h68 (security : ℕ) (mass : (Fin 4 → _root_.CurrentAFT.ActualControls.Palette security) → ℝ)
    (selected : Finset (Fin 4)) (bound : ℝ) (hb : 0 ≤ bound) (hmass : ∀ word, |mass word| ≤ bound)
    (output : Fin selected.card → _root_.CurrentAFT.ActualControls.Palette security) (centers : Fin 0 → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |(_root_.CurrentAFT.LocalCoefficientFamily.selectedKernel security selected.card mass selected (by simp)).val output centers| ≤
      _root_.CurrentAFT.LocalCoefficientPointBounds.selectedBound security bound := by
  have hcard : selected.card ≤ 4 := (Finset.card_le_card (Finset.subset_univ selected)).trans_eq (by simp)
  have hq : (1 : ℝ) ≤ _root_.CurrentAFT.Parameters.modulus security := by
    exact_mod_cast (_root_.CurrentAFT.Parameters.modulus_spec security).2.two_le.trans' (by omega)
  have hM := _p2mH192 security
  have hqpow := pow_le_pow_right₀ hq hcard
  have hfour : (1 : ℝ) ≤ 4 * (_root_.CurrentAFT.Parameters.modulus security : ℝ) := by linarith
  have hfourpow := pow_le_pow_right₀ hfour hcard
  have hMpow : (_root_.CurrentAFT.RationalTensorInverseProgram.actualBound security)^selected.card ≤
      (1 + _root_.CurrentAFT.RationalTensorInverseProgram.actualBound security)^4 :=
    (pow_le_pow_left₀ hM (show _root_.CurrentAFT.RationalTensorInverseProgram.actualBound security ≤
        1 + _root_.CurrentAFT.RationalTensorInverseProgram.actualBound security by linarith) selected.card).trans
      (pow_le_pow_right₀ (by linarith) hcard)
  apply (_p2mH67 security mass selected bound hb hmass output centers).trans
  exact mul_le_mul (mul_le_mul hqpow hMpow (pow_nonneg hM _) (by positivity))
    (mul_le_mul_of_nonneg_left hfourpow (by positivity)) (by positivity) (by positivity)
open _root_.P2M60f02c0e renaming h68 → _p2mH68
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h63 (security : ℕ) : 0 ≤ _root_.CurrentAFT.LocalCoefficientPointBounds.numeratorBound security :=
  mul_nonneg (by norm_num) (_p2mH66 security _ (by positivity))
open _root_.P2M60f02c0e renaming h63 → _p2mH63
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h64 (security order : ℕ) (roots : _root_.CurrentAFT.RootTaggedSelected.RootPair security)
    (primaryColor : _root_.CurrentAFT.ActualControls.Palette security) (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order)
    (colors : Fin arity.val.1.val → _root_.CurrentAFT.ActualControls.Palette security) (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |(_root_.CurrentAFT.LocalRaisingLinear.completeFamilyLinear security order
        (_root_.CurrentAFT.RootMassColumns.primaryMassAt security roots (_root_.CurrentAFT.CoefficientHilbert.centerLinear (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (Pi.single primaryColor 1)))
          arity).val colors centers| ≤ _root_.CurrentAFT.LocalCoefficientPointBounds.numeratorBound security := by
  rw [_p2mH128 security order _
    (_p2mH130 security roots primaryColor)]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _selected ∈ (Finset.univ : Finset (Finset (Fin 4))).erase ∅,
        _root_.CurrentAFT.LocalCoefficientPointBounds.selectedBound security (2 * (_root_.CurrentAFT.Parameters.modulus security : ℝ)^2) := by
      apply Finset.sum_le_sum
      intro selected _
      unfold _root_.CurrentAFT.RationalLocalFamilyProgram.insertSelected
      split_ifs with hmatch
      · exact _p2mH68 security _ selected _ (by positivity)
          (fun word => by
            simpa only [mul_one] using _p2mH178 security roots
              (_root_.CurrentAFT.CoefficientHilbert.centerLinear (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (Pi.single primaryColor 1)) 1 (by norm_num)
              (_p2mH162 security primaryColor) word)
          (colors ∘ finCongr hmatch.1) Fin.elim0
      · simpa only [abs_zero] using _p2mH66 security (2 * (_root_.CurrentAFT.Parameters.modulus security : ℝ)^2) (by positivity)
    _ ≤ _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (_p2mH66 security _ (by positivity))
      apply Nat.cast_le.mpr
      calc
        _ ≤ (Finset.univ : Finset (Finset (Fin 4))).card := Finset.card_le_card (Finset.erase_subset ..)
        _ = 16 := by norm_num
open _root_.P2M60f02c0e renaming h64 → _p2mH64
end
open _root_.P2M60f02c0e renaming h63 → _p2mH63
open _root_.P2M60f02c0e renaming h64 → _p2mH64
open _root_.P2M60f02c0e renaming h65 → _p2mH65
open _root_.P2M60f02c0e renaming h66 → _p2mH66
open _root_.P2M60f02c0e renaming h67 → _p2mH67
open _root_.P2M60f02c0e renaming h68 → _p2mH68
open _root_.P2M60f02c0e renaming h69 → _p2mH69
end CurrentAFT.LocalCoefficientPointBounds
open _root_.P2M60f02c0e renaming h63 → _p2mH63
open _root_.P2M60f02c0e renaming h64 → _p2mH64
open _root_.P2M60f02c0e renaming h65 → _p2mH65
open _root_.P2M60f02c0e renaming h66 → _p2mH66
open _root_.P2M60f02c0e renaming h67 → _p2mH67
open _root_.P2M60f02c0e renaming h68 → _p2mH68
open _root_.P2M60f02c0e renaming h69 → _p2mH69
end
open _root_.P2M60f02c0e renaming h63 → _p2mH63
open _root_.P2M60f02c0e renaming h64 → _p2mH64
open _root_.P2M60f02c0e renaming h65 → _p2mH65
open _root_.P2M60f02c0e renaming h66 → _p2mH66
open _root_.P2M60f02c0e renaming h67 → _p2mH67
open _root_.P2M60f02c0e renaming h68 → _p2mH68
open _root_.P2M60f02c0e renaming h69 → _p2mH69
namespace CurrentAFT.ActualCoordinateBounds
end CurrentAFT.ActualCoordinateBounds
section
namespace CurrentAFT.PositiveFamilyPointBound
open AFT ProposalPrimary ActualControls LocalCoefficientFamily NormalizedLocalPolynomial
  LocalRaisingBounds GradedControlAlgebra GradedControlNorm GradedControlStability GradedInverseNorm
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.PositiveFamilyPointBound.classicalFinDecidableEq
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h79 (security order : ℕ) :
    _root_.CurrentAFT.LocalRaisingBounds.coefficientNorm security order (_root_.CurrentAFT.NormalizedLocalPolynomial.positiveFamily security order (_root_.CurrentAFT.NormalizedLocalPolynomial.independentPositiveLaw security)) ≤
      1 + _root_.CurrentAFT.LocalRaisingBounds.positiveConstant := by
  have hadd := _root_.CurrentAFT.GradedControlStability.familyNorm_add_le (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order
    (_root_.CurrentAFT.BackgroundRates.primaryFactor security) (_root_.CurrentAFT.BackgroundRates.bodyFactor security)
    (_root_.CurrentAFT.RaisingPatternBudget.primaryFactor_pos security).le (_root_.CurrentAFT.RaisingPatternBudget.bodyFactor_pos security).le
    (_root_.CurrentAFT.NormalizedLocalPolynomial.positiveFamily security order (_root_.CurrentAFT.NormalizedLocalPolynomial.independentPositiveLaw security) - 1) 1
  rw [sub_add_cancel, _root_.CurrentAFT.GradedInverseNorm.familyNorm_one] at hadd
  have hbase : (1 : ℝ) ≤ _root_.CurrentAFT.Parameters.base security := by
    exact_mod_cast (show 1 ≤ _root_.CurrentAFT.Parameters.base security by have := _root_.CurrentAFT.Parameters.base_ge_two security; omega)
  have hden : (1 : ℝ) ≤ (_root_.CurrentAFT.Parameters.base security : ℝ)^39 := one_le_pow₀ hbase
  have hd := (_root_.CurrentAFT.LocalRaisingBounds.independentPositive_defect security order).trans
    (div_le_self _root_.CurrentAFT.LocalRaisingBounds.positiveConstant_nonneg hden)
  change _root_.CurrentAFT.LocalRaisingBounds.coefficientNorm security order _ ≤ _root_.CurrentAFT.LocalRaisingBounds.coefficientNorm security order _ + 1 at hadd
  linarith
open _root_.P2M60f02c0e renaming h79 → _p2mH79
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h80 (security order : ℕ) (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order)
    (colors : Fin arity.val.1.val → _root_.CurrentAFT.ActualControls.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |((_root_.CurrentAFT.NormalizedLocalPolynomial.positiveFamily security order (_root_.CurrentAFT.NormalizedLocalPolynomial.independentPositiveLaw security)) arity).val colors centers| ≤ _root_.CurrentAFT.PositiveFamilyPointBound.bound security order :=
  (_p2mH9 security order _ arity colors centers).trans
    (mul_le_mul_of_nonneg_left (_p2mH79 security order) (by positivity))
open _root_.P2M60f02c0e renaming h80 → _p2mH80
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h78 (security order : ℕ) : 0 ≤ _root_.CurrentAFT.PositiveFamilyPointBound.bound security order := by
  unfold _root_.CurrentAFT.PositiveFamilyPointBound.bound
  positivity [_root_.CurrentAFT.LocalRaisingBounds.positiveConstant_nonneg]
open _root_.P2M60f02c0e renaming h78 → _p2mH78
end
open _root_.P2M60f02c0e renaming h78 → _p2mH78
open _root_.P2M60f02c0e renaming h79 → _p2mH79
open _root_.P2M60f02c0e renaming h80 → _p2mH80
end CurrentAFT.PositiveFamilyPointBound
open _root_.P2M60f02c0e renaming h78 → _p2mH78
open _root_.P2M60f02c0e renaming h79 → _p2mH79
open _root_.P2M60f02c0e renaming h80 → _p2mH80
end
open _root_.P2M60f02c0e renaming h78 → _p2mH78
open _root_.P2M60f02c0e renaming h79 → _p2mH79
open _root_.P2M60f02c0e renaming h80 → _p2mH80
section
namespace CurrentAFT.RationalActualFamilyApproximation
open AFT GradedControlAlgebra ActualControls BackgroundFamilies
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RationalActualFamilyApproximation.approximationFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h84 (security order : ℕ) (first second : _root_.CurrentAFT.BackgroundFamilies.ActualFamily security order) :
    _root_.CurrentAFT.RationalFamilyProductProgram.product order (_root_.CurrentAFT.RationalActualFamilyApproximation.data security order first) (_root_.CurrentAFT.RationalActualFamilyApproximation.data security order second) =
      _root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.GradedControlAlgebra.familyProduct (_root_.CurrentAFT.ProposalPrimary.primaryLaw security)
        (_root_.CurrentAFT.ActualControls.bodyReference security) order first second) :=
  _p2mH100 _ _ _ _ _
open _root_.P2M60f02c0e renaming h84 → _p2mH84
end
open _root_.P2M60f02c0e renaming h84 → _p2mH84
end CurrentAFT.RationalActualFamilyApproximation
open _root_.P2M60f02c0e renaming h84 → _p2mH84
end
open _root_.P2M60f02c0e renaming h84 → _p2mH84
namespace CurrentAFT.BackgroundFamilies
end CurrentAFT.BackgroundFamilies
namespace CurrentAFT.BackgroundFamilies.bodyArity
end CurrentAFT.BackgroundFamilies.bodyArity
namespace CurrentAFT.BackgroundFamilies.bodyCoefficient
end CurrentAFT.BackgroundFamilies.bodyCoefficient
namespace CurrentAFT.BackgroundFamilies.bodyFamily
end CurrentAFT.BackgroundFamilies.bodyFamily
namespace CurrentAFT.BackgroundFamilies.bodyKernel
end CurrentAFT.BackgroundFamilies.bodyKernel
namespace CurrentAFT.BackgroundFamilies.freeCertificate
end CurrentAFT.BackgroundFamilies.freeCertificate
namespace CurrentAFT.BackgroundFamilies.primaryArity
end CurrentAFT.BackgroundFamilies.primaryArity
namespace CurrentAFT.BackgroundFamilies.primaryCoefficient
end CurrentAFT.BackgroundFamilies.primaryCoefficient
namespace CurrentAFT.BackgroundFamilies.primaryFamily
end CurrentAFT.BackgroundFamilies.primaryFamily
namespace CurrentAFT.BackgroundFamilies.primaryKernel
end CurrentAFT.BackgroundFamilies.primaryKernel
namespace CurrentAFT.BackgroundFamilies.translationCertificate
end CurrentAFT.BackgroundFamilies.translationCertificate
section
namespace CurrentAFT.RationalBackgroundTable
open AFT ControlCoordinates ControlProduct GradedControlAlgebra BackgroundFamilies
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalBackgroundTable.tableFinDecidableEq
set_option maxRecDepth 8192
private theorem _root_.P2M60f02c0e.h263 (order : ℕ) (horder : 1 ≤ order) (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) :
    arity = _root_.CurrentAFT.BackgroundFamilies.primaryArity order horder ↔ arity.val.1.val = 1 ∧ arity.val.2.val = 0 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · intro h
    apply Subtype.ext
    exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
open _root_.P2M60f02c0e renaming h263 → _p2mH263
set_option maxRecDepth 8192
private theorem _root_.P2M60f02c0e.h262 (order : ℕ) (horder : 1 ≤ order) (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) :
    arity = _root_.CurrentAFT.BackgroundFamilies.bodyArity order horder ↔ arity.val.1.val = 0 ∧ arity.val.2.val = 1 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · intro h
    apply Subtype.ext
    exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
open _root_.P2M60f02c0e renaming h262 → _p2mH262
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h85 {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body) (order : ℕ) (horder : 1 ≤ order)
    (first : Primary → ℝ) (second : Body → ℝ)
    (hf : ∑ color, primary.weight color*first color = 0) (hs : ∑ color, body.weight color*second color = 0) :
    _root_.CurrentAFT.RationalBackgroundTable.firstTable order first second = fun arity =>
      ((_root_.CurrentAFT.BackgroundFamilies.primaryFamily primary body order horder first hf+_root_.CurrentAFT.BackgroundFamilies.bodyFamily primary body order horder second hs) arity).val := by
  funext arity colors centers
  by_cases hp : arity = _root_.CurrentAFT.BackgroundFamilies.primaryArity order horder
  · subst arity
    simp [_root_.CurrentAFT.RationalBackgroundTable.firstTable, _root_.CurrentAFT.BackgroundFamilies.primaryFamily, _root_.CurrentAFT.BackgroundFamilies.bodyFamily, _root_.CurrentAFT.BackgroundFamilies.primaryArity, _root_.CurrentAFT.BackgroundFamilies.bodyArity, _root_.CurrentAFT.BackgroundFamilies.primaryKernel, _root_.CurrentAFT.BackgroundFamilies.bodyKernel]
  · by_cases hb : arity = _root_.CurrentAFT.BackgroundFamilies.bodyArity order horder
    · subst arity
      simp [_root_.CurrentAFT.RationalBackgroundTable.firstTable, _root_.CurrentAFT.BackgroundFamilies.primaryFamily, _root_.CurrentAFT.BackgroundFamilies.bodyFamily, _root_.CurrentAFT.BackgroundFamilies.primaryArity, _root_.CurrentAFT.BackgroundFamilies.bodyArity, _root_.CurrentAFT.BackgroundFamilies.primaryKernel, _root_.CurrentAFT.BackgroundFamilies.bodyKernel]
    · have hfirst := mt (_p2mH263 order horder arity).mpr hp
      have hsecond := mt (_p2mH262 order horder arity).mpr hb
      simp only [_root_.CurrentAFT.RationalBackgroundTable.firstTable, dif_neg hfirst, dif_neg hsecond, Pi.add_apply, _root_.CurrentAFT.BackgroundFamilies.primaryFamily, _root_.CurrentAFT.BackgroundFamilies.bodyFamily,
        Pi.single_eq_of_ne hp, Pi.single_eq_of_ne hb, Submodule.coe_zero, Pi.zero_apply, add_zero]
open _root_.P2M60f02c0e renaming h85 → _p2mH85
end
open _root_.P2M60f02c0e renaming h85 → _p2mH85
open _root_.P2M60f02c0e renaming h262 → _p2mH262
open _root_.P2M60f02c0e renaming h263 → _p2mH263
end CurrentAFT.RationalBackgroundTable
open _root_.P2M60f02c0e renaming h85 → _p2mH85
open _root_.P2M60f02c0e renaming h262 → _p2mH262
open _root_.P2M60f02c0e renaming h263 → _p2mH263
end
open _root_.P2M60f02c0e renaming h85 → _p2mH85
section
namespace CurrentAFT.RationalFamilyProductProgram
open AFT GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h105 {Primary Body : Type*} (order : ℕ) (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order)
    (colors : Fin arity.val.1.val → Primary) (centers : Fin arity.val.2.val → Body) :
    |_root_.CurrentAFT.RationalFamilyProductProgram.unit (Scalar := ℝ) order arity colors centers| ≤ 1 := by
  unfold _root_.CurrentAFT.RationalFamilyProductProgram.unit
  split_ifs <;> norm_num
open _root_.P2M60f02c0e renaming h105 → _p2mH105
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h99 {Primary Body : Type*} (order : ℕ) (table : _root_.CurrentAFT.RationalFamilyProductProgram.Table ℝ Primary Body order)
    (bound scale : ℝ) (hb : 0 ≤ bound) (hs : 1 ≤ scale)
    (hscale : (Nat.card (_root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) : ℝ)^2 * bound ≤ scale)
    (htable : ∀ arity colors centers, |table arity colors centers| ≤ bound) (count : ℕ)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → Primary)
    (centers : Fin arity.val.2.val → Body) :
    |_root_.CurrentAFT.RationalFamilyProductProgram.power order table count arity colors centers| ≤ scale^count := by
  induction count generalizing arity colors centers with
  | zero => simpa only [_root_.CurrentAFT.RationalFamilyProductProgram.power, pow_zero] using _p2mH105 order arity colors centers
  | succ count ih =>
      have h := _p2mH101 order (_root_.CurrentAFT.RationalFamilyProductProgram.power order table count) table (scale^count) bound
        (pow_nonneg (by linarith) _) hb ih htable arity colors centers
      simp only [Fintype.card_eq_nat_card] at h
      apply h.trans
      have hm := mul_le_mul_of_nonneg_left hscale (pow_nonneg (by linarith : 0 ≤ scale) count)
      rw [pow_succ scale count]
      convert hm using 1
      ring
open _root_.P2M60f02c0e renaming h99 → _p2mH99
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h94 (order : ℕ) (bound error : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error) :
    1 ≤ _root_.CurrentAFT.RationalFamilyProductProgram.growth order bound error := by
  unfold _root_.CurrentAFT.RationalFamilyProductProgram.growth
  exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (by positivity))
open _root_.P2M60f02c0e renaming h94 → _p2mH94
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h95 (order : ℕ) (bound error : ℝ) :
    (Nat.card (_root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) : ℝ)^2 * (bound + error + 1) ≤ _root_.CurrentAFT.RationalFamilyProductProgram.growth order bound error := by
  unfold _root_.CurrentAFT.RationalFamilyProductProgram.growth
  linarith
open _root_.P2M60f02c0e renaming h95 → _p2mH95
end
open _root_.P2M60f02c0e renaming h94 → _p2mH94
open _root_.P2M60f02c0e renaming h95 → _p2mH95
open _root_.P2M60f02c0e renaming h99 → _p2mH99
open _root_.P2M60f02c0e renaming h105 → _p2mH105
end CurrentAFT.RationalFamilyProductProgram
open _root_.P2M60f02c0e renaming h94 → _p2mH94
open _root_.P2M60f02c0e renaming h95 → _p2mH95
open _root_.P2M60f02c0e renaming h99 → _p2mH99
open _root_.P2M60f02c0e renaming h105 → _p2mH105
end
open _root_.P2M60f02c0e renaming h94 → _p2mH94
open _root_.P2M60f02c0e renaming h95 → _p2mH95
open _root_.P2M60f02c0e renaming h99 → _p2mH99
open _root_.P2M60f02c0e renaming h105 → _p2mH105
section
namespace CurrentAFT.RationalFamilyProductProgram
open AFT GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h103 {Primary Body : Type*} (order : ℕ) (table : _root_.CurrentAFT.RationalFamilyProductProgram.Table ℝ Primary Body order)
    (bound : ℝ) (hb : 0 ≤ bound)
    (htable : ∀ arity colors centers, |table arity colors centers| ≤ bound)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → Primary)
    (centers : Fin arity.val.2.val → Body) :
    |_root_.CurrentAFT.RationalFamilyProductProgram.reciprocal order table arity colors centers| ≤
      ((order+1 : ℕ):ℝ) * (_root_.CurrentAFT.RationalFamilyProductProgram.growth order (1+bound) 0)^order := by
  let scale := _root_.CurrentAFT.RationalFamilyProductProgram.growth order (1+bound) 0
  have hs : 1 ≤ scale := _p2mH94 order (1+bound) 0 (by positivity) (by norm_num)
  have htable' (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → Primary)
      (centers : Fin arity.val.2.val → Body) :
      |(_root_.CurrentAFT.RationalFamilyProductProgram.unit order - table : _root_.CurrentAFT.RationalFamilyProductProgram.Table ℝ Primary Body order) arity colors centers| ≤ 1+bound :=
    (abs_sub _ _).trans (add_le_add (_p2mH105 order arity colors centers) (htable arity colors centers))
  have hscale : (Nat.card (_root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) : ℝ)^2 * (1+bound) ≤ scale := by
    dsimp [scale, _root_.CurrentAFT.RationalFamilyProductProgram.growth]
    nlinarith [sq_nonneg (Nat.card (_root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) : ℝ)]
  unfold _root_.CurrentAFT.RationalFamilyProductProgram.reciprocal
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _count ∈ Finset.range (order+1), scale^order := by
      apply Finset.sum_le_sum
      intro count hcount
      exact (_p2mH99 order (_root_.CurrentAFT.RationalFamilyProductProgram.unit order - table) (1+bound) scale (by positivity) hs hscale
        htable' count arity colors centers).trans (pow_le_pow_right₀ hs (by
          have := Finset.mem_range.mp hcount; omega))
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; rfl
open _root_.P2M60f02c0e renaming h103 → _p2mH103
end
open _root_.P2M60f02c0e renaming h103 → _p2mH103
end CurrentAFT.RationalFamilyProductProgram
open _root_.P2M60f02c0e renaming h103 → _p2mH103
end
open _root_.P2M60f02c0e renaming h103 → _p2mH103
namespace CurrentAFT.RationalActualFamilyApproximation
end CurrentAFT.RationalActualFamilyApproximation
section
namespace CurrentAFT.RationalFamilyWordProduct
open AFT ActualControls ControlCoordinates GradedControlAlgebra RationalFamilyProductProgram
open scoped BigOperators
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalFamilyWordProduct.wordProductFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h106 (security order count : ℕ) (families : Fin count → _root_.CurrentAFT.BackgroundFamilies.ActualFamily security order) :
    _root_.CurrentAFT.RationalFamilyWordProduct.current order count (fun index arity => (families index arity).val) =
      fun arity => ((∏ index, families index) arity).val := by
  induction count with
  | zero => simpa only [_root_.CurrentAFT.RationalFamilyWordProduct.current, Fin.prod_univ_zero] using _p2mH104 (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order
  | succ count ih =>
    rw [_root_.CurrentAFT.RationalFamilyWordProduct.current, ih, _p2mH100, Fin.prod_univ_succ]
    have hm : (∏ index : Fin count, families index.succ) * families 0 =
        families 0 * (∏ index : Fin count, families index.succ) := mul_comm _ _
    change (fun arity => (((∏ index : Fin count, families index.succ) * families 0) arity).val) =
      (fun arity => ((families 0 * (∏ index : Fin count, families index.succ)) arity).val)
    rw [hm]
open _root_.P2M60f02c0e renaming h106 → _p2mH106
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h107 {Primary Body : Type*} (order count : ℕ) (tables : Fin count → _root_.CurrentAFT.RationalFamilyProductProgram.Table ℝ Primary Body order)
    (bound scale : ℝ) (hb : 0 ≤ bound) (hs : 1 ≤ scale)
    (hscale : (Nat.card (_root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) : ℝ)^2 * bound ≤ scale)
    (htable : ∀ index arity colors centers, |tables index arity colors centers| ≤ bound)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → Primary) (centers : Fin arity.val.2.val → Body) :
    |_root_.CurrentAFT.RationalFamilyWordProduct.current order count tables arity colors centers| ≤ scale^count := by
  induction count generalizing arity colors centers with
  | zero => simpa only [_root_.CurrentAFT.RationalFamilyWordProduct.current, pow_zero] using _p2mH105 order arity colors centers
  | succ count ih =>
    have ht := ih (fun index => tables index.succ) (fun index => htable index.succ)
    have h := _p2mH101 order (_root_.CurrentAFT.RationalFamilyWordProduct.current order count (fun index => tables index.succ)) (tables 0)
      (scale^count) bound (by positivity) hb ht (htable 0) arity colors centers
    simp only [Fintype.card_eq_nat_card] at h
    apply h.trans
    have hm := mul_le_mul_of_nonneg_left hscale (pow_nonneg (by linarith : 0 ≤ scale) count)
    rw [pow_succ scale count]
    convert hm using 1
    ring
open _root_.P2M60f02c0e renaming h107 → _p2mH107
end
open _root_.P2M60f02c0e renaming h106 → _p2mH106
open _root_.P2M60f02c0e renaming h107 → _p2mH107
end CurrentAFT.RationalFamilyWordProduct
open _root_.P2M60f02c0e renaming h106 → _p2mH106
open _root_.P2M60f02c0e renaming h107 → _p2mH107
end
open _root_.P2M60f02c0e renaming h106 → _p2mH106
open _root_.P2M60f02c0e renaming h107 → _p2mH107
namespace CurrentAFT.RationalPositiveReferenceProgram
end CurrentAFT.RationalPositiveReferenceProgram
section
namespace CurrentAFT.RationalLegMassProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion
open PositiveFirstCoefficient (positiveTripleLaw positiveFourLaw consEquiv)
open PairedReferenceEnergy (compensatorAt)
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalLegMassProgram.classicalFinDecidableEq
attribute [local irreducible] Parameters.base primaryLaw centerLaw PublicParameterProgram.modulus
attribute [local irreducible] rootReference ActualBlockFock.primaryLawAt
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h126 (security : ℕ) : 0 ≤ _root_.CurrentAFT.RationalLegMassProgram.atRootErrorConstant security := by
  unfold _root_.CurrentAFT.RationalLegMassProgram.atRootErrorConstant _root_.CurrentAFT.RationalPositiveReferenceProgram.fixedErrorConstant _root_.CurrentAFT.RationalRootMassProgram.primaryErrorConstant
  positivity
open _root_.P2M60f02c0e renaming h126 → _p2mH126
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h127 (security : ℕ) :
    0 ≤ _root_.CurrentAFT.RationalLegMassProgram.meanErrorConstant security ∧ 0 ≤ _root_.CurrentAFT.RationalLegMassProgram.differenceErrorConstant security := by
  have h := _p2mH126 security
  have hmean : 0 ≤ _root_.CurrentAFT.RationalLegMassProgram.meanErrorConstant security := by unfold _root_.CurrentAFT.RationalLegMassProgram.meanErrorConstant; positivity
  exact ⟨hmean, add_nonneg h hmean⟩
open _root_.P2M60f02c0e renaming h127 → _p2mH127
end
open _root_.P2M60f02c0e renaming h126 → _p2mH126
open _root_.P2M60f02c0e renaming h127 → _p2mH127
end CurrentAFT.RationalLegMassProgram
open _root_.P2M60f02c0e renaming h126 → _p2mH126
open _root_.P2M60f02c0e renaming h127 → _p2mH127
end
open _root_.P2M60f02c0e renaming h126 → _p2mH126
open _root_.P2M60f02c0e renaming h127 → _p2mH127
section
namespace CurrentAFT.RationalMassLiftProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls RationalProposalProgram
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h133 (security : ℕ) (profile : _root_.CurrentAFT.ActualControls.Palette security → ℝ) (output : _root_.CurrentAFT.ActualControls.Palette security) :
    _root_.CurrentAFT.RationalMassLiftProgram.actual security profile output = (_root_.CurrentAFT.FirstResponse.responseEquiv security).symm profile output /
      (_root_.CurrentAFT.DiffuseProfiles.activation security * (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight output) := by
  change _root_.CurrentAFT.PrimaryTensorInverse.densityInverse security (_root_.CurrentAFT.RootTaggedLocal.profileDensity security profile) output = _
  rw [_root_.CurrentAFT.PrimaryTensorInverse.densityInverse_apply]
  have hprofile : (fun color => (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color * _root_.CurrentAFT.RootTaggedLocal.profileDensity security profile color) = profile := by
    funext color
    rw [_root_.CurrentAFT.RootTaggedLocal.profileDensity_apply]
    field_simp [(_root_.CurrentAFT.ActualControls.primaryReference_positive security color).ne']
  rw [hprofile]
  ring
open _root_.P2M60f02c0e renaming h133 → _p2mH133
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h132 (security : ℕ) (output : _root_.CurrentAFT.ActualControls.Palette security) :
    1 / (8 * (_root_.CurrentAFT.Parameters.base security : ℝ) * _root_.CurrentAFT.Parameters.modulus security) ≤
      _root_.CurrentAFT.DiffuseProfiles.activation security * (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight output := by
  have hb := _root_.CurrentAFT.FirstResponse.base_pos security
  have hq := _root_.CurrentAFT.FirstResponse.modulus_pos security
  have hp : 1 / (2 * (_root_.CurrentAFT.Parameters.modulus security : ℝ)) ≤ (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight output := by
    simpa only [_root_.CurrentAFT.ProposalPrimary.primaryLaw] using _root_.CurrentAFT.ProposalPrimary.primaryProfile_atom_lower security output
  calc
    _ = (1 / (4 * (_root_.CurrentAFT.Parameters.base security : ℝ))) * (1 / (2 * (_root_.CurrentAFT.Parameters.modulus security : ℝ))) := by ring
    _ ≤ _ := mul_le_mul (_root_.CurrentAFT.FirstResponse.activation_lower_simple security) hp (by positivity) (_root_.CurrentAFT.DiffuseProfiles.activation_pos security).le
open _root_.P2M60f02c0e renaming h132 → _p2mH132
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h131 (security : ℕ) (profile : _root_.CurrentAFT.ActualControls.Palette security → ℝ) (bound : ℝ) (hb : 0 ≤ bound)
    (hprofile : ∀ color, |profile color| ≤ bound) (output : _root_.CurrentAFT.ActualControls.Palette security) :
    |_root_.CurrentAFT.RationalMassLiftProgram.actual security profile output| ≤ _root_.CurrentAFT.RationalTensorInverseProgram.actualBound security * bound := by
  have hq := _root_.CurrentAFT.FirstResponse.modulus_pos security
  have hbase := _root_.CurrentAFT.FirstResponse.base_pos security
  have hden := _p2mH132 security output
  have hpos : 0 < _root_.CurrentAFT.DiffuseProfiles.activation security * (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight output :=
    mul_pos (_root_.CurrentAFT.DiffuseProfiles.activation_pos security) (_root_.CurrentAFT.ActualControls.primaryReference_positive security output)
  rw [_p2mH133, abs_div, abs_of_pos hpos]
  calc
    _ ≤ (_root_.CurrentAFT.RationalDensityInverseProgram.inverseBound security * bound) /
      (_root_.CurrentAFT.DiffuseProfiles.activation security * (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight output) :=
      div_le_div_of_nonneg_right
        (_p2mH92 security profile bound hb hprofile output) hpos.le
    _ ≤ (_root_.CurrentAFT.RationalDensityInverseProgram.inverseBound security * bound) /
      (1 / (8 * (_root_.CurrentAFT.Parameters.base security : ℝ) * _root_.CurrentAFT.Parameters.modulus security)) :=
      div_le_div_of_nonneg_left (by unfold _root_.CurrentAFT.RationalDensityInverseProgram.inverseBound; positivity) (by positivity) hden
    _ = _ := by unfold _root_.CurrentAFT.RationalTensorInverseProgram.actualBound; ring_nf; simp only [inv_inv]
open _root_.P2M60f02c0e renaming h131 → _p2mH131
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h135 (security : ℕ) (profile : _root_.CurrentAFT.ActualControls.Palette security → ℝ) (word : Fin 1 → _root_.CurrentAFT.ActualControls.Palette security) :
    _root_.CurrentAFT.PrimaryTensorInverse.massLift security 1 (_root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile profile) word =
      _root_.CurrentAFT.RationalMassLiftProgram.actual security profile (word 0) := by
  unfold _root_.CurrentAFT.PrimaryTensorInverse.massLift
  change _root_.CurrentAFT.PrimaryTensorInverse.densityInverse security
    (fun color => _root_.CurrentAFT.PrimaryTensorInverse.massDensity security 1 (_root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile profile)
      (Fin.cons color Fin.elim0)) (word 0) =
    _root_.CurrentAFT.PrimaryTensorInverse.densityInverse security (_root_.CurrentAFT.RootTaggedLocal.profileDensity security profile) (word 0)
  apply congrArg (fun input : _root_.CurrentAFT.ActualControls.Palette security → ℝ => _root_.CurrentAFT.PrimaryTensorInverse.densityInverse security input (word 0))
  funext color
  simp only [_root_.CurrentAFT.PrimaryTensorInverse.massDensity, _root_.CurrentAFT.PrimaryTensorInverse.referenceWeight, _root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile,
    Fin.prod_univ_one, Fin.cons_zero, _root_.CurrentAFT.RootTaggedLocal.profileDensity_apply]
open _root_.P2M60f02c0e renaming h135 → _p2mH135
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h134 (security : ℕ) : 0 ≤ _root_.CurrentAFT.RationalMassLiftProgram.errorConstant security := by
  unfold _root_.CurrentAFT.RationalMassLiftProgram.errorConstant _root_.CurrentAFT.RationalDensityInverseProgram.inverseBound _root_.CurrentAFT.RationalFirstResponseProgram.inverseErrorConstant
  positivity
open _root_.P2M60f02c0e renaming h134 → _p2mH134
end
open _root_.P2M60f02c0e renaming h131 → _p2mH131
open _root_.P2M60f02c0e renaming h132 → _p2mH132
open _root_.P2M60f02c0e renaming h133 → _p2mH133
open _root_.P2M60f02c0e renaming h134 → _p2mH134
open _root_.P2M60f02c0e renaming h135 → _p2mH135
end CurrentAFT.RationalMassLiftProgram
open _root_.P2M60f02c0e renaming h131 → _p2mH131
open _root_.P2M60f02c0e renaming h132 → _p2mH132
open _root_.P2M60f02c0e renaming h133 → _p2mH133
open _root_.P2M60f02c0e renaming h134 → _p2mH134
open _root_.P2M60f02c0e renaming h135 → _p2mH135
end
open _root_.P2M60f02c0e renaming h131 → _p2mH131
open _root_.P2M60f02c0e renaming h132 → _p2mH132
open _root_.P2M60f02c0e renaming h133 → _p2mH133
open _root_.P2M60f02c0e renaming h134 → _p2mH134
open _root_.P2M60f02c0e renaming h135 → _p2mH135
namespace CurrentAFT.RationalBackgroundProfiles
end CurrentAFT.RationalBackgroundProfiles
namespace CurrentAFT.RationalBackgroundProfiles.bodyDeviation
end CurrentAFT.RationalBackgroundProfiles.bodyDeviation
namespace CurrentAFT.RationalBackgroundProfiles.colors
end CurrentAFT.RationalBackgroundProfiles.colors
namespace CurrentAFT.RationalBackgroundProfiles.convolution
end CurrentAFT.RationalBackgroundProfiles.convolution
namespace CurrentAFT.RationalBackgroundProfiles.inverseShift
end CurrentAFT.RationalBackgroundProfiles.inverseShift
namespace CurrentAFT.RationalBackgroundProfiles.margin
end CurrentAFT.RationalBackgroundProfiles.margin
namespace CurrentAFT.RationalBackgroundProfiles.projected
end CurrentAFT.RationalBackgroundProfiles.projected
namespace CurrentAFT.RationalBackgroundProfiles.residual
end CurrentAFT.RationalBackgroundProfiles.residual
namespace CurrentAFT.RationalBackgroundProfiles.seedProfile
end CurrentAFT.RationalBackgroundProfiles.seedProfile
namespace CurrentAFT.RationalMassLiftProgram
end CurrentAFT.RationalMassLiftProgram
namespace CurrentAFT.RationalMassLiftProgram.current
end CurrentAFT.RationalMassLiftProgram.current
section
namespace CurrentAFT.RationalRootProfileProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles ProposalPrimary ActualControls
  RootTaggedLocal
open UniformBodyProfiles (BodyRole preRootLaw)
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base primaryLaw centerLaw
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h180 (security : ℕ) : 1 ≤ _root_.CurrentAFT.RationalRootProfileProgram.preRootError security := by
  have h : 0 ≤ _root_.CurrentAFT.RationalRootMassProgram.primaryErrorConstant security * (_root_.CurrentAFT.Parameters.modulus security : ℝ) := by
    unfold _root_.CurrentAFT.RationalRootMassProgram.primaryErrorConstant
    positivity
  unfold _root_.CurrentAFT.RationalRootProfileProgram.preRootError
  linarith
open _root_.P2M60f02c0e renaming h180 → _p2mH180
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h179 (security : ℕ) :
    0 ≤ _root_.CurrentAFT.RationalRootProfileProgram.firstErrorConstant security ∧ 0 ≤ _root_.CurrentAFT.RationalRootProfileProgram.meanErrorConstant security := by
  have hp := _p2mH180 security
  have hm := _p2mH134 security
  have ha := _p2mH192 security
  constructor
  · unfold _root_.CurrentAFT.RationalRootProfileProgram.firstErrorConstant; positivity
  · unfold _root_.CurrentAFT.RationalRootProfileProgram.meanErrorConstant; positivity
open _root_.P2M60f02c0e renaming h179 → _p2mH179
end
open _root_.P2M60f02c0e renaming h179 → _p2mH179
open _root_.P2M60f02c0e renaming h180 → _p2mH180
end CurrentAFT.RationalRootProfileProgram
open _root_.P2M60f02c0e renaming h179 → _p2mH179
open _root_.P2M60f02c0e renaming h180 → _p2mH180
end
open _root_.P2M60f02c0e renaming h179 → _p2mH179
open _root_.P2M60f02c0e renaming h180 → _p2mH180
namespace CurrentAFT.LocalCoefficientPointBounds
end CurrentAFT.LocalCoefficientPointBounds
namespace CurrentAFT.PositiveFamilyPointBound
end CurrentAFT.PositiveFamilyPointBound
namespace CurrentAFT.RationalPositiveFamilyProgram
end CurrentAFT.RationalPositiveFamilyProgram
section
namespace CurrentAFT.RationalNormalizedPrimaryProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls CoefficientHilbert
  ControlCoordinates GradedControlAlgebra RationalFamilyProductProgram
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RationalNormalizedPrimaryProgram.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalNormalizedPrimaryProgram.classicalSubtypeDecidableEq
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h138 (security order : ℕ) :
    _root_.CurrentAFT.RationalFamilyProductProgram.reciprocal order (fun arity =>
      (_root_.CurrentAFT.NormalizedLocalPolynomial.positiveFamily security order (_root_.CurrentAFT.NormalizedLocalPolynomial.independentPositiveLaw security) arity).val) =
      fun arity => (_root_.CurrentAFT.LocalRaisingBounds.positiveInverse security order arity).val := by
  rw [_p2mH102]
  rfl
open _root_.P2M60f02c0e renaming h138 → _p2mH138
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h137 (security order : ℕ) : 0 ≤ _root_.CurrentAFT.RationalNormalizedPrimaryProgram.inverseBound security order := by
  unfold _root_.CurrentAFT.RationalNormalizedPrimaryProgram.inverseBound
  positivity [_p2mH94 order (1 + _root_.CurrentAFT.PositiveFamilyPointBound.bound security order) 0
    (by positivity [_p2mH78 security order]) (by norm_num)]
open _root_.P2M60f02c0e renaming h137 → _p2mH137
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h136 (security order : ℕ) (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order)
    (colors : Fin arity.val.1.val → _root_.CurrentAFT.ActualControls.Palette security) (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |(_root_.CurrentAFT.LocalRaisingBounds.positiveInverse security order arity).val colors centers| ≤ _root_.CurrentAFT.RationalNormalizedPrimaryProgram.inverseBound security order := by
  have h := _p2mH103 order
    (fun arity => (_root_.CurrentAFT.NormalizedLocalPolynomial.positiveFamily security order
      (_root_.CurrentAFT.NormalizedLocalPolynomial.independentPositiveLaw security) arity).val)
    (_root_.CurrentAFT.PositiveFamilyPointBound.bound security order) (_p2mH78 security order)
    (_p2mH80 security order) arity colors centers
  rw [_p2mH138] at h
  exact h
open _root_.P2M60f02c0e renaming h136 → _p2mH136
end
open _root_.P2M60f02c0e renaming h136 → _p2mH136
open _root_.P2M60f02c0e renaming h137 → _p2mH137
open _root_.P2M60f02c0e renaming h138 → _p2mH138
end CurrentAFT.RationalNormalizedPrimaryProgram
open _root_.P2M60f02c0e renaming h136 → _p2mH136
open _root_.P2M60f02c0e renaming h137 → _p2mH137
open _root_.P2M60f02c0e renaming h138 → _p2mH138
end
open _root_.P2M60f02c0e renaming h136 → _p2mH136
open _root_.P2M60f02c0e renaming h137 → _p2mH137
open _root_.P2M60f02c0e renaming h138 → _p2mH138
namespace CurrentAFT.RationalBackgroundTable
end CurrentAFT.RationalBackgroundTable
namespace CurrentAFT.RationalBackgroundTable.firstTable
end CurrentAFT.RationalBackgroundTable.firstTable
namespace CurrentAFT.RationalNormalizedPrimaryProgram
end CurrentAFT.RationalNormalizedPrimaryProgram
namespace CurrentAFT.RationalRootProfileProgram
end CurrentAFT.RationalRootProfileProgram
namespace CurrentAFT.RationalRootProfileProgram.approximatePreRoot
end CurrentAFT.RationalRootProfileProgram.approximatePreRoot
namespace CurrentAFT.RationalRootProfileProgram.deviation
end CurrentAFT.RationalRootProfileProgram.deviation
namespace CurrentAFT.RationalRootProfileProgram.mean
end CurrentAFT.RationalRootProfileProgram.mean
namespace CurrentAFT.RationalRootProfileProgram.meanDeviation
end CurrentAFT.RationalRootProfileProgram.meanDeviation
namespace CurrentAFT.RationalRootProfileProgram.preRoot
end CurrentAFT.RationalRootProfileProgram.preRoot
namespace CurrentAFT.RationalRootProfileProgram.preRoot.match_1
end CurrentAFT.RationalRootProfileProgram.preRoot.match_1
namespace CurrentAFT.RationalRootProfileProgram.shifted
end CurrentAFT.RationalRootProfileProgram.shifted
section
namespace CurrentAFT.RationalSingletonProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls RootTaggedLocal
  ControlCoordinates GradedControlAlgebra RationalFamilyProductProgram
open UniformBodyProfiles (BodyRole)
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalSingletonProgram.programFinDecidableEq
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h186 {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body) (order : ℕ) (horder : 1 ≤ order)
    (density : Primary → ℝ) (hcenter : ∑ color, primary.weight color * density color = 0) :
    _root_.CurrentAFT.RationalBackgroundTable.firstTable order density (fun _ : Body => 0) =
      fun arity => (_root_.CurrentAFT.BackgroundFamilies.primaryFamily primary body order horder density hcenter arity).val := by
  have hz : ∑ color, body.weight color * (0 : ℝ) = 0 := by simp
  have hk : _root_.CurrentAFT.BackgroundFamilies.bodyKernel primary body (fun _ => 0) hz = 0 := by
    apply Subtype.ext
    rfl
  rw [_p2mH85 primary body order horder density (fun _ => 0) hcenter hz]
  simp only [_root_.CurrentAFT.BackgroundFamilies.bodyFamily, hk, Pi.single_zero, add_zero]
open _root_.P2M60f02c0e renaming h186 → _p2mH186
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h189 (security order : ℕ) (horder : 1 ≤ order)
    (profile : _root_.CurrentAFT.ActualControls.Palette security → ℝ) (hzero : ∑ color, profile color = 0) :
    _root_.CurrentAFT.PrimaryMassFamilies.massCertificateFamily security order 1 horder
      (_root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile profile)
      (_root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile_centered profile hzero)
      (_root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile_symmetric profile) =
      _root_.CurrentAFT.BackgroundFamilies.primaryFamily (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order horder
        (_root_.CurrentAFT.RationalMassLiftProgram.actual security profile)
        (by
          change (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).expectation (_root_.CurrentAFT.RationalMassLiftProgram.actual security profile) = 0
          rw [_root_.CurrentAFT.RationalMassLiftProgram.actual, LinearMap.comp_apply,
            _root_.CurrentAFT.PrimaryTensorInverse.densityInverse_mean, _root_.CurrentAFT.RootTaggedLocal.profileDensity_mean, hzero, mul_zero]) := by
  unfold _root_.CurrentAFT.PrimaryMassFamilies.massCertificateFamily _root_.CurrentAFT.BackgroundFamilies.primaryFamily
  change Pi.single (M := fun arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order =>
      _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) arity.val.1.val arity.val.2.val)
    (_root_.CurrentAFT.BackgroundFamilies.primaryArity order horder)
    (_root_.CurrentAFT.PrimaryMassFamilies.massLiftKernel security 1 (_root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile profile)
      (_root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile_centered profile hzero)
      (_root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile_symmetric profile)) = _
  congr 1
  apply Subtype.ext
  funext colors centers
  exact _p2mH135 security profile colors
open _root_.P2M60f02c0e renaming h189 → _p2mH189
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h190 (security order : ℕ) (horder : 1 ≤ order) (role : _root_.CurrentAFT.UniformBodyProfiles.BodyRole) (queue : ℤ) :
    _root_.CurrentAFT.RationalBackgroundTable.firstTable order
      (_root_.CurrentAFT.RationalMassLiftProgram.actual security (_root_.CurrentAFT.RootMeanPrimary.meanProfile security role queue))
      (fun _ : _root_.CurrentAFT.ActualControls.SafePalette security => 0) =
      fun arity => (_root_.CurrentAFT.RootMeanPrimary.positiveAtom security order horder role queue arity).val := by
  unfold _root_.CurrentAFT.RootMeanPrimary.positiveAtom
  rw [_p2mH189 security order horder _ (_root_.CurrentAFT.RootMeanPrimary.meanProfile_mass security role queue)]
  exact _p2mH186 _ _ _ _ _ _
open _root_.P2M60f02c0e renaming h190 → _p2mH190
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h187 (security order : ℕ) (horder : 1 ≤ order) (role : _root_.CurrentAFT.UniformBodyProfiles.BodyRole) (queue : ℤ)
    (root : _root_.CurrentAFT.CycleRootExpansion.Root security) :
    _root_.CurrentAFT.RationalBackgroundTable.firstTable order (_root_.CurrentAFT.RootReferenceColumns.singletonDensityAt security role queue root)
      (fun _ : _root_.CurrentAFT.ActualControls.SafePalette security => 0) =
      fun arity => (_root_.CurrentAFT.RootReferenceColumns.singletonFirstAt security order horder role queue root arity).val := by
  exact _p2mH186 _ _ _ _ _ _
open _root_.P2M60f02c0e renaming h187 → _p2mH187
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h185 {Primary Body : Type*} (order : ℕ) (density : Primary → ℝ) (bound : ℝ)
    (hb : 0 ≤ bound) (hdensity : ∀ color, |density color| ≤ bound)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → Primary)
    (centers : Fin arity.val.2.val → Body) :
    |_root_.CurrentAFT.RationalBackgroundTable.firstTable order density (fun _ => 0) arity colors centers| ≤ bound := by
  unfold _root_.CurrentAFT.RationalBackgroundTable.firstTable
  split_ifs
  · exact hdensity _
  · simpa only [abs_zero] using hb
  · simpa only [abs_zero] using hb
open _root_.P2M60f02c0e renaming h185 → _p2mH185
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h191 (security : ℕ) (role : _root_.CurrentAFT.UniformBodyProfiles.BodyRole) (queue : ℤ) (root : _root_.CurrentAFT.CycleRootExpansion.Root security)
    (output : _root_.CurrentAFT.ActualControls.Palette security) : |_root_.CurrentAFT.RootTaggedLocal.deviationProfile security role queue root output| ≤ 2 ∧
      |_root_.CurrentAFT.RootMeanPrimary.meanProfile security role queue output| ≤ 2 := by
  have hatom (law : _root_.AFT.FiniteDist (_root_.CurrentAFT.ActualControls.Palette security)) : |law.weight output| ≤ 1 := by
    rw [abs_of_nonneg (law.nonneg output)]
    exact law.atom_le_one output
  constructor
  · exact (abs_sub _ _).trans ((add_le_add (hatom _) (hatom _)).trans_eq (by norm_num))
  · exact (abs_sub _ _).trans ((add_le_add (hatom _) (hatom _)).trans_eq (by norm_num))
open _root_.P2M60f02c0e renaming h191 → _p2mH191
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h184 (security : ℕ) : 0 ≤ _root_.CurrentAFT.RationalSingletonProgram.firstBound security := by
  exact mul_nonneg (by norm_num) (_p2mH192 security)
open _root_.P2M60f02c0e renaming h184 → _p2mH184
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h181 (security order : ℕ) (horder : 1 ≤ order) (role : _root_.CurrentAFT.UniformBodyProfiles.BodyRole) (queue : ℤ)
    (root : _root_.CurrentAFT.CycleRootExpansion.Root security) (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order)
    (colors : Fin arity.val.1.val → _root_.CurrentAFT.ActualControls.Palette security) (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |(_root_.CurrentAFT.RootReferenceColumns.singletonFirstAt security order horder role queue root arity).val colors centers| ≤ _root_.CurrentAFT.RationalSingletonProgram.firstBound security := by
  rw [← congrFun (congrFun (congrFun (_p2mH187 security order horder role queue root) arity) colors) centers]
  apply _p2mH185 _ _ _ (_p2mH184 security)
  intro output
  exact (_p2mH131 security (_root_.CurrentAFT.RootTaggedLocal.deviationProfile security role queue root) 2 (by norm_num)
    (fun color => (_p2mH191 security role queue root color).1) output).trans_eq (by unfold _root_.CurrentAFT.RationalSingletonProgram.firstBound; ring)
open _root_.P2M60f02c0e renaming h181 → _p2mH181
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h183 (security order : ℕ) (horder : 1 ≤ order) (role : _root_.CurrentAFT.UniformBodyProfiles.BodyRole) (queue : ℤ)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.ActualControls.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |(_root_.CurrentAFT.RootMeanPrimary.positiveFamily security order horder role queue arity).val colors centers| ≤ _root_.CurrentAFT.RationalSingletonProgram.positiveBound security := by
  have hm : |(_root_.CurrentAFT.RootMeanPrimary.positiveAtom security order horder role queue arity).val colors centers| ≤ _root_.CurrentAFT.RationalSingletonProgram.firstBound security := by
    rw [← congrFun (congrFun (congrFun (_p2mH190 security order horder role queue) arity) colors) centers]
    apply _p2mH185 _ _ _ (_p2mH184 security)
    intro output
    exact (_p2mH131 security (_root_.CurrentAFT.RootMeanPrimary.meanProfile security role queue) 2 (by norm_num)
      (fun color => (_p2mH191 security role queue 0 color).2) output).trans_eq (by unfold _root_.CurrentAFT.RationalSingletonProgram.firstBound; ring)
  have hu : |((1 : _root_.CurrentAFT.LocalCoefficientFamily.Family security order) arity).val colors centers| ≤ 1 := by
    rw [← congrFun (congrFun (congrFun (_p2mH104 (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order) arity) colors) centers]
    unfold _root_.CurrentAFT.RationalFamilyProductProgram.unit
    split_ifs <;> norm_num
  exact (abs_add_le _ _).trans (add_le_add hu hm)
open _root_.P2M60f02c0e renaming h183 → _p2mH183
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h188 (security order : ℕ) (horder : 1 ≤ order) (role : _root_.CurrentAFT.UniformBodyProfiles.BodyRole) (queue : ℤ) :
    _root_.CurrentAFT.RationalFamilyProductProgram.reciprocal order (fun arity => (_root_.CurrentAFT.RootMeanPrimary.positiveFamily security order horder role queue arity).val) =
      fun arity => (_root_.CurrentAFT.RootMeanPrimary.positiveInverse security order horder role queue arity).val := by
  rw [_p2mH102]
  rfl
open _root_.P2M60f02c0e renaming h188 → _p2mH188
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h182 (security order : ℕ) (horder : 1 ≤ order) (role : _root_.CurrentAFT.UniformBodyProfiles.BodyRole) (queue : ℤ)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.ActualControls.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |(_root_.CurrentAFT.RootMeanPrimary.positiveInverse security order horder role queue arity).val colors centers| ≤ _root_.CurrentAFT.RationalSingletonProgram.inverseBound security order := by
  have h := _p2mH103 order (fun arity => (_root_.CurrentAFT.RootMeanPrimary.positiveFamily security order horder role queue arity).val)
    (_root_.CurrentAFT.RationalSingletonProgram.positiveBound security) (by unfold _root_.CurrentAFT.RationalSingletonProgram.positiveBound; positivity [_p2mH184 security])
    (_p2mH183 security order horder role queue) arity colors centers
  rw [_p2mH188] at h
  exact h
open _root_.P2M60f02c0e renaming h182 → _p2mH182
end
open _root_.P2M60f02c0e renaming h181 → _p2mH181
open _root_.P2M60f02c0e renaming h182 → _p2mH182
open _root_.P2M60f02c0e renaming h183 → _p2mH183
open _root_.P2M60f02c0e renaming h184 → _p2mH184
open _root_.P2M60f02c0e renaming h185 → _p2mH185
open _root_.P2M60f02c0e renaming h186 → _p2mH186
open _root_.P2M60f02c0e renaming h187 → _p2mH187
open _root_.P2M60f02c0e renaming h188 → _p2mH188
open _root_.P2M60f02c0e renaming h189 → _p2mH189
open _root_.P2M60f02c0e renaming h190 → _p2mH190
open _root_.P2M60f02c0e renaming h191 → _p2mH191
end CurrentAFT.RationalSingletonProgram
open _root_.P2M60f02c0e renaming h181 → _p2mH181
open _root_.P2M60f02c0e renaming h182 → _p2mH182
open _root_.P2M60f02c0e renaming h183 → _p2mH183
open _root_.P2M60f02c0e renaming h184 → _p2mH184
open _root_.P2M60f02c0e renaming h185 → _p2mH185
open _root_.P2M60f02c0e renaming h186 → _p2mH186
open _root_.P2M60f02c0e renaming h187 → _p2mH187
open _root_.P2M60f02c0e renaming h188 → _p2mH188
open _root_.P2M60f02c0e renaming h189 → _p2mH189
open _root_.P2M60f02c0e renaming h190 → _p2mH190
open _root_.P2M60f02c0e renaming h191 → _p2mH191
end
open _root_.P2M60f02c0e renaming h181 → _p2mH181
open _root_.P2M60f02c0e renaming h182 → _p2mH182
open _root_.P2M60f02c0e renaming h183 → _p2mH183
open _root_.P2M60f02c0e renaming h184 → _p2mH184
open _root_.P2M60f02c0e renaming h185 → _p2mH185
open _root_.P2M60f02c0e renaming h186 → _p2mH186
open _root_.P2M60f02c0e renaming h187 → _p2mH187
open _root_.P2M60f02c0e renaming h188 → _p2mH188
open _root_.P2M60f02c0e renaming h189 → _p2mH189
open _root_.P2M60f02c0e renaming h190 → _p2mH190
open _root_.P2M60f02c0e renaming h191 → _p2mH191
namespace CurrentAFT.LegCoefficientPointBounds
end CurrentAFT.LegCoefficientPointBounds
namespace CurrentAFT.RationalLegMassProgram
end CurrentAFT.RationalLegMassProgram
namespace CurrentAFT.RationalLegMassProgram.difference
end CurrentAFT.RationalLegMassProgram.difference
namespace CurrentAFT.RationalMassLiftProgram.actual
end CurrentAFT.RationalMassLiftProgram.actual
namespace CurrentAFT.RationalSingletonProgram
end CurrentAFT.RationalSingletonProgram
namespace CurrentAFT.RationalSingletonProgram.first
end CurrentAFT.RationalSingletonProgram.first
namespace CurrentAFT.RationalSingletonProgram.positive
end CurrentAFT.RationalSingletonProgram.positive
namespace CurrentAFT.RootMeanPrimary
end CurrentAFT.RootMeanPrimary
namespace CurrentAFT.RootMeanPrimary.positiveAtom
end CurrentAFT.RootMeanPrimary.positiveAtom
namespace CurrentAFT.RootMeanPrimary.positiveFamily
end CurrentAFT.RootMeanPrimary.positiveFamily
namespace CurrentAFT.RootReferenceColumns.singletonFirstAt
end CurrentAFT.RootReferenceColumns.singletonFirstAt
section
namespace CurrentAFT.RationalUnselectedLegProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates GradedControlAlgebra
  RationalFamilyProductProgram RationalActualFamilyApproximation
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalUnselectedLegProgram.classicalFinDecidableEq
attribute [local irreducible] Parameters.base primaryLaw centerLaw
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h203 (security : ℕ) (root : ℤ) (word : Fin 3 → _root_.CurrentAFT.ActualControls.Palette security) :
    |(_root_.CurrentAFT.ActualBlockFock.primaryLawAt security root).weight word - _root_.CurrentAFT.RootTaggedLegHigher.rawMassLinear security 1 word| ≤ 2 := by
  have hmean : _root_.CurrentAFT.RootTaggedLegHigher.rawMassLinear security 1 word = (_root_.CurrentAFT.RootLegReciprocal.meanPositiveLaw security).weight word :=
    (congrFun (_root_.CurrentAFT.RootLegReciprocal.meanPositiveLaw_weight security) word).symm
  rw [hmean]
  have hfirst : |(_root_.CurrentAFT.ActualBlockFock.primaryLawAt security root).weight word| ≤ 1 := by
    rw [abs_of_nonneg ((_root_.CurrentAFT.ActualBlockFock.primaryLawAt security root).nonneg word)]
    exact (_root_.CurrentAFT.ActualBlockFock.primaryLawAt security root).atom_le_one word
  have hsecond : |(_root_.CurrentAFT.RootLegReciprocal.meanPositiveLaw security).weight word| ≤ 1 := by
    rw [abs_of_nonneg ((_root_.CurrentAFT.RootLegReciprocal.meanPositiveLaw security).nonneg word)]
    exact (_root_.CurrentAFT.RootLegReciprocal.meanPositiveLaw security).atom_le_one word
  exact (abs_sub _ _).trans ((add_le_add hfirst hsecond).trans_eq (by norm_num))
open _root_.P2M60f02c0e renaming h203 → _p2mH203
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h200 (security : ℕ) : 0 ≤ _root_.CurrentAFT.RationalUnselectedLegProgram.higherError security ∧ 0 ≤ _root_.CurrentAFT.RationalUnselectedLegProgram.positiveError security := by
  constructor
  · unfold _root_.CurrentAFT.RationalUnselectedLegProgram.higherError _root_.CurrentAFT.RationalLegFamilyTable.higherError
    exact Finset.sum_nonneg (fun selected _ => _p2mH125 security selected.card 2 _
      (by norm_num) (_p2mH127 security).2)
  · unfold _root_.CurrentAFT.RationalUnselectedLegProgram.positiveError _root_.CurrentAFT.RationalLegFamilyTable.positiveError
    exact Finset.sum_nonneg (fun selected _ => _p2mH125 security selected.card 1 _
      (by norm_num) (_p2mH127 security).1)
open _root_.P2M60f02c0e renaming h200 → _p2mH200
end
open _root_.P2M60f02c0e renaming h200 → _p2mH200
open _root_.P2M60f02c0e renaming h203 → _p2mH203
end CurrentAFT.RationalUnselectedLegProgram
open _root_.P2M60f02c0e renaming h200 → _p2mH200
open _root_.P2M60f02c0e renaming h203 → _p2mH203
end
open _root_.P2M60f02c0e renaming h200 → _p2mH200
open _root_.P2M60f02c0e renaming h203 → _p2mH203
namespace CurrentAFT.RationalUnselectedLegProgram
end CurrentAFT.RationalUnselectedLegProgram
section
namespace CurrentAFT.RationalUnselectedLegProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates GradedControlAlgebra
  RationalFamilyProductProgram RationalActualFamilyApproximation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RationalUnselectedLegProgram.normalizedFinDecidableEq
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h205 (security : ℕ) : 0 ≤ _root_.CurrentAFT.RationalUnselectedLegProgram.positiveBound security := by
  unfold _root_.CurrentAFT.RationalUnselectedLegProgram.positiveBound
  positivity [_p2mH58 security 1 (by norm_num)]
open _root_.P2M60f02c0e renaming h205 → _p2mH205
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h199 (security order : ℕ) (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order)
    (colors : Fin arity.val.1.val → _root_.CurrentAFT.ActualControls.Palette security) (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |(_root_.CurrentAFT.RootLegReciprocal.positive security order arity).val colors centers| ≤ _root_.CurrentAFT.RationalUnselectedLegProgram.positiveBound security :=
  _p2mH57 security order (_root_.CurrentAFT.RootLegReciprocal.meanPositiveLaw security) arity colors centers
open _root_.P2M60f02c0e renaming h199 → _p2mH199
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h201 (security order : ℕ) :
    _root_.CurrentAFT.RationalFamilyProductProgram.reciprocal order (fun arity => (_root_.CurrentAFT.RootLegReciprocal.positive security order arity).val) =
      fun arity => (_root_.CurrentAFT.RootLegReciprocal.reciprocal security order arity).val := by
  rw [_p2mH102]
  rfl
open _root_.P2M60f02c0e renaming h201 → _p2mH201
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h202 (security order : ℕ) : 0 ≤ _root_.CurrentAFT.RationalUnselectedLegProgram.inverseBound security order ∧ 0 ≤ _root_.CurrentAFT.RationalUnselectedLegProgram.inverseError security order := by
  have hA := _p2mH205 security
  have hE := (_p2mH200 security).2
  have hg0 := _p2mH94 order (1 + _root_.CurrentAFT.RationalUnselectedLegProgram.positiveBound security) 0 (by positivity) (by norm_num)
  have hg := _p2mH94 order (1 + _root_.CurrentAFT.RationalUnselectedLegProgram.positiveBound security) (_root_.CurrentAFT.RationalUnselectedLegProgram.positiveError security) (by positivity) hE
  constructor
  · unfold _root_.CurrentAFT.RationalUnselectedLegProgram.inverseBound; positivity
  · unfold _root_.CurrentAFT.RationalUnselectedLegProgram.inverseError; positivity
open _root_.P2M60f02c0e renaming h202 → _p2mH202
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h197 (security order : ℕ) (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order)
    (colors : Fin arity.val.1.val → _root_.CurrentAFT.ActualControls.Palette security) (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |(_root_.CurrentAFT.RootLegReciprocal.reciprocal security order arity).val colors centers| ≤ _root_.CurrentAFT.RationalUnselectedLegProgram.inverseBound security order := by
  have h := _p2mH103 order (fun arity => (_root_.CurrentAFT.RootLegReciprocal.positive security order arity).val)
    (_root_.CurrentAFT.RationalUnselectedLegProgram.positiveBound security) (_p2mH205 security) (_p2mH199 security order) arity colors centers
  rw [_p2mH201] at h
  exact h
open _root_.P2M60f02c0e renaming h197 → _p2mH197
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h204 (security : ℕ) : 0 ≤ _root_.CurrentAFT.RationalUnselectedLegProgram.numeratorBound security ∧ 0 ≤ _root_.CurrentAFT.RationalUnselectedLegProgram.numeratorError security := by
  exact ⟨add_nonneg (_p2mH184 security)
    (mul_nonneg (by norm_num) (_p2mH58 security 2 (by norm_num))),
    add_nonneg (_p2mH179 security).1 (_p2mH200 security).1⟩
open _root_.P2M60f02c0e renaming h204 → _p2mH204
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h198 (security order : ℕ) (horder : 1 ≤ order) (root : _root_.CurrentAFT.CycleRootExpansion.Root security)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.ActualControls.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |(_root_.CurrentAFT.RationalUnselectedLegProgram.numeratorActual security order horder root arity).val colors centers| ≤ _root_.CurrentAFT.RationalUnselectedLegProgram.numeratorBound security := by
  exact (abs_add_le _ _).trans (add_le_add
    (_p2mH181 security order horder .attachment 0 root arity colors centers)
    (_p2mH54 security order _ 2 (by norm_num) (_p2mH203 security root.val) arity colors centers))
open _root_.P2M60f02c0e renaming h198 → _p2mH198
end
open _root_.P2M60f02c0e renaming h197 → _p2mH197
open _root_.P2M60f02c0e renaming h198 → _p2mH198
open _root_.P2M60f02c0e renaming h199 → _p2mH199
open _root_.P2M60f02c0e renaming h201 → _p2mH201
open _root_.P2M60f02c0e renaming h202 → _p2mH202
open _root_.P2M60f02c0e renaming h204 → _p2mH204
open _root_.P2M60f02c0e renaming h205 → _p2mH205
end CurrentAFT.RationalUnselectedLegProgram
open _root_.P2M60f02c0e renaming h197 → _p2mH197
open _root_.P2M60f02c0e renaming h198 → _p2mH198
open _root_.P2M60f02c0e renaming h199 → _p2mH199
open _root_.P2M60f02c0e renaming h201 → _p2mH201
open _root_.P2M60f02c0e renaming h202 → _p2mH202
open _root_.P2M60f02c0e renaming h204 → _p2mH204
open _root_.P2M60f02c0e renaming h205 → _p2mH205
end
open _root_.P2M60f02c0e renaming h197 → _p2mH197
open _root_.P2M60f02c0e renaming h198 → _p2mH198
open _root_.P2M60f02c0e renaming h199 → _p2mH199
open _root_.P2M60f02c0e renaming h201 → _p2mH201
open _root_.P2M60f02c0e renaming h202 → _p2mH202
open _root_.P2M60f02c0e renaming h204 → _p2mH204
open _root_.P2M60f02c0e renaming h205 → _p2mH205
section
namespace CurrentAFT.WeightedPointKernelProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls CanonicalReconstruction
  ControlCoordinates ControlProduct GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.WeightedPointKernelProgram.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.WeightedPointKernelProgram.safeDecidableEq
attribute [local irreducible] Parameters.base primaryLaw bodyReference
section Generic
variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h258 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color)
    {r s : ℕ} (sourcePrimary : Fin r → Primary) (sourceBody : Fin s → Body) :
    ((∏ index, primary.weight (sourcePrimary index)) * (∏ index, body.weight (sourceBody index))) •
      (_root_.CurrentAFT.CanonicalReconstruction.pointKernel primary body hp hb sourcePrimary sourceBody).val =
        _root_.CurrentAFT.ControlProduct.symmetrize (_root_.CurrentAFT.WeightedPointKernelProgram.weightedTensor primary body sourcePrimary sourceBody) := by
  have hraw : ((∏ index, primary.weight (sourcePrimary index)) * (∏ index, body.weight (sourceBody index))) •
      _root_.CurrentAFT.CanonicalReconstruction.pointTensor primary body sourcePrimary sourceBody = _root_.CurrentAFT.WeightedPointKernelProgram.weightedTensor primary body sourcePrimary sourceBody := by
    funext colors centers
    simp only [Pi.smul_apply, smul_eq_mul, _root_.CurrentAFT.CanonicalReconstruction.pointTensor, _root_.CurrentAFT.WeightedPointKernelProgram.weightedTensor]
    rw [← _p2mH24 primary hp, ← _p2mH24 body hb]
    ring
  have h := congrArg (_root_.CurrentAFT.ControlProduct.symmetrizeLinear (Primary := Primary) (Body := Body)) hraw
  rw [map_smul] at h
  exact h
open _root_.P2M60f02c0e renaming h258 → _p2mH258
end Generic
open _root_.P2M60f02c0e renaming h258 → _p2mH258
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h257 (security : ℕ) {r s : ℕ} (sourcePrimary : Fin r → _root_.CurrentAFT.ActualControls.Palette security)
    (sourceBody : Fin s → _root_.CurrentAFT.ActualControls.SafePalette security) (colors : Fin r → _root_.CurrentAFT.ActualControls.Palette security) (centers : Fin s → _root_.CurrentAFT.ActualControls.SafePalette security) :
    (_root_.CurrentAFT.WeightedPointKernelProgram.actualKernel security sourcePrimary sourceBody).val colors centers =
      _root_.CurrentAFT.RationalFamilyProductProgram.average r s (fun primaryOrder bodyOrder =>
        (∏ index, ((if colors (primaryOrder index) = sourcePrimary index then (1 : ℝ) else 0) -
          (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight (sourcePrimary index))) *
        ∏ index, ((if centers (bodyOrder index) = sourceBody index then (1 : ℝ) else 0) -
          (_root_.CurrentAFT.ActualControls.bodyReference security).weight (sourceBody index))) := by
  have h := congrFun (congrFun (_p2mH258 (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security)
    (_root_.CurrentAFT.ActualControls.primaryReference_positive security) (_root_.CurrentAFT.ActualControls.bodyReference_positive security) sourcePrimary sourceBody) colors) centers
  change (_root_.CurrentAFT.WeightedPointKernelProgram.actualKernel security sourcePrimary sourceBody).val colors centers = _ at h
  rw [_root_.CurrentAFT.ControlProduct.symmetrize_apply] at h
  simp only [Fintype.card_perm, Fintype.card_fin, _root_.CurrentAFT.WeightedPointKernelProgram.weightedTensor, _root_.AFT.MixedKernel.canonicalPointBasis] at h
  rw [h]
  unfold _root_.CurrentAFT.RationalFamilyProductProgram.average
  apply congrArg (fun total : ℝ => (r.factorial : ℝ)⁻¹ * (s.factorial : ℝ)⁻¹ * total)
  apply Finset.sum_congr (by ext; simp)
  intro primaryOrder _
  apply Finset.sum_congr (by ext; simp)
  intro bodyOrder _
  try dsimp only
  apply congrArg₂ (fun first second : ℝ => first * second)
  · apply Finset.prod_congr (by ext; simp)
    intro index _
    by_cases hequal : colors (primaryOrder index) = sourcePrimary index <;>
      simp only [Function.comp_apply, hequal, if_true, if_false]
  · apply Finset.prod_congr (by ext; simp)
    intro index _
    by_cases hequal : centers (bodyOrder index) = sourceBody index <;>
      simp only [Function.comp_apply, hequal, if_true, if_false]
open _root_.P2M60f02c0e renaming h257 → _p2mH257
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h256 (security : ℕ) {r s : ℕ} (sourcePrimary : Fin r → _root_.CurrentAFT.ActualControls.Palette security)
    (sourceBody : Fin s → _root_.CurrentAFT.ActualControls.SafePalette security) (colors : Fin r → _root_.CurrentAFT.ActualControls.Palette security) (centers : Fin s → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |(_root_.CurrentAFT.WeightedPointKernelProgram.actualKernel security sourcePrimary sourceBody).val colors centers| ≤ 1 := by
  rw [_p2mH257]
  apply _p2mH93
  intro primaryOrder bodyOrder
  rw [abs_mul, Finset.abs_prod, Finset.abs_prod]
  have hproduct {Index Color : Type} [Fintype Index] [Fintype Color] (law : _root_.AFT.FiniteDist Color)
      (source output : Index → Color) :
      (∏ index, |(if output index = source index then (1 : ℝ) else 0) - law.weight (source index)|) ≤ 1 := by
    apply Finset.prod_le_one
    · intro _ _
      exact abs_nonneg _
    · intro index _
      have hlo := law.nonneg (source index)
      have hhi := law.atom_le_one (source index)
      split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
  exact (mul_le_mul (hproduct (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) sourcePrimary (fun index => colors (primaryOrder index)))
    (hproduct (_root_.CurrentAFT.ActualControls.bodyReference security) sourceBody (fun index => centers (bodyOrder index)))
    (Finset.prod_nonneg fun _ _ => abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
open _root_.P2M60f02c0e renaming h256 → _p2mH256
end
open _root_.P2M60f02c0e renaming h256 → _p2mH256
open _root_.P2M60f02c0e renaming h257 → _p2mH257
open _root_.P2M60f02c0e renaming h258 → _p2mH258
end CurrentAFT.WeightedPointKernelProgram
open _root_.P2M60f02c0e renaming h256 → _p2mH256
open _root_.P2M60f02c0e renaming h257 → _p2mH257
open _root_.P2M60f02c0e renaming h258 → _p2mH258
end
open _root_.P2M60f02c0e renaming h256 → _p2mH256
open _root_.P2M60f02c0e renaming h257 → _p2mH257
open _root_.P2M60f02c0e renaming h258 → _p2mH258
namespace CurrentAFT.CoefficientHilbert
end CurrentAFT.CoefficientHilbert
namespace CurrentAFT.CoefficientHilbert.centerLinear
end CurrentAFT.CoefficientHilbert.centerLinear
namespace CurrentAFT.RationalOrdinaryProfileProgram
end CurrentAFT.RationalOrdinaryProfileProgram
namespace CurrentAFT.RationalOrdinaryProfileProgram.preRoot
end CurrentAFT.RationalOrdinaryProfileProgram.preRoot
namespace CurrentAFT.RationalOrdinaryProfileProgram.shifted
end CurrentAFT.RationalOrdinaryProfileProgram.shifted
namespace CurrentAFT.WeightedPointKernelProgram
end CurrentAFT.WeightedPointKernelProgram
namespace CurrentAFT.WeightedPointKernelProgram.current
end CurrentAFT.WeightedPointKernelProgram.current
namespace CurrentAFT.WeightedPointKernelProgram.weightedTensor
end CurrentAFT.WeightedPointKernelProgram.weightedTensor
section
namespace CurrentAFT.RationalOrdinaryFamilyProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion CoefficientHilbert
  ControlCoordinates GradedControlAlgebra RationalFamilyProductProgram RationalActualFamilyApproximation
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalOrdinaryFamilyProgram.ordinaryFamilyFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalOrdinaryFamilyProgram.ordinaryFamilySafeDecidableEq
attribute [local irreducible] Parameters.base primaryLaw centerLaw PublicParameterProgram.modulus
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h146 (security order : ℕ) (horder : 1 ≤ order) (source : _root_.CurrentAFT.ActualControls.SafePalette security) (root : _root_.CurrentAFT.CycleRootExpansion.Root security) :
    _root_.CurrentAFT.RationalBackgroundTable.firstTable order (_root_.CurrentAFT.RootReferenceColumns.ordinaryDensityAt security root (Pi.single source 1))
      (fun _ : _root_.CurrentAFT.ActualControls.SafePalette security => 0) = fun arity => (_root_.CurrentAFT.RationalOrdinaryFamilyProgram.firstActual security order horder source root arity).val :=
  _p2mH186 _ _ _ _ _ _
open _root_.P2M60f02c0e renaming h146 → _p2mH146
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h144 (security order : ℕ) (horder : 1 ≤ order) (source : _root_.CurrentAFT.ActualControls.SafePalette security) :
    _root_.CurrentAFT.RationalBackgroundTable.firstTable order (fun _ : _root_.CurrentAFT.ActualControls.Palette security => 0)
      (_root_.CurrentAFT.CoefficientHilbert.centerLinear (_root_.CurrentAFT.ActualControls.bodyReference security) (Pi.single source 1)) =
      fun arity => (_root_.CurrentAFT.RaisingChannels.bodyLeading security order horder (Pi.single source 1) arity).val := by
  have hz : ∑ color, (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color * (0 : ℝ) = 0 := by simp
  have hk : _root_.CurrentAFT.BackgroundFamilies.primaryKernel (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) (fun _ => 0) hz = 0 := by
    apply Subtype.ext; rfl
  rw [_p2mH85 _ _ _ _ _ _ hz (_root_.CurrentAFT.CoefficientHilbert.center_mean _ _)]
  simp only [_root_.CurrentAFT.BackgroundFamilies.primaryFamily, hk, Pi.single_zero, zero_add]
  rfl
open _root_.P2M60f02c0e renaming h144 → _p2mH144
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h145 {Color : Type*} [Fintype Color] (law : _root_.AFT.FiniteDist Color) (source color : Color) :
    |_root_.CurrentAFT.CoefficientHilbert.centerLinear law (Pi.single source 1) color| ≤ 1 := by
  have hlo := law.nonneg source
  have hhi := law.atom_le_one source
  simp only [_root_.CurrentAFT.CoefficientHilbert.centerLinear, LinearMap.coe_mk, AddHom.coe_mk, _root_.AFT.FiniteDist.expectation, Pi.single_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
open _root_.P2M60f02c0e renaming h145 → _p2mH145
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h148 {Source Output : Type*} [Fintype Source] [Fintype Output]
    (law : _root_.AFT.FiniteDist Source) (embedding : Source → Output) (score : Source → ℝ)
    (hscore : ∀ source, |score source| ≤ 1) (output : Output) :
    |_root_.CurrentAFT.SelectedOrdinaryRoot.pushLinear law embedding score output| ≤ 1 := by
  change |∑ source, if embedding source = output then law.weight source * score source else 0| ≤ 1
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ source, law.weight source := by
      apply Finset.sum_le_sum
      intro source _
      split_ifs
      · rw [abs_mul, abs_of_nonneg (law.nonneg source)]
        exact (mul_le_mul_of_nonneg_left (hscore source) (law.nonneg source)).trans_eq (mul_one _)
      · simpa only [abs_zero] using law.nonneg source
    _ = 1 := law.sum_one
open _root_.P2M60f02c0e renaming h148 → _p2mH148
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h141 (security : ℕ) (source : _root_.CurrentAFT.ActualControls.SafePalette security) (root : _root_.CurrentAFT.CycleRootExpansion.Root security) (output : _root_.CurrentAFT.ActualControls.Palette security) :
    |_root_.CurrentAFT.RootReferenceColumns.ordinaryDensityAt security root (Pi.single source 1) output| ≤ _root_.CurrentAFT.RationalTensorInverseProgram.actualBound security := by
  have hprofile (color : _root_.CurrentAFT.ActualControls.Palette security) :
      |_root_.CurrentAFT.RootMassColumns.ordinaryMassAt security root (_root_.CurrentAFT.CoefficientHilbert.centerLinear (_root_.CurrentAFT.ActualControls.bodyReference security) (Pi.single source 1)) color| ≤ 1 :=
    _p2mH148 (_root_.CurrentAFT.ActualControls.bodyReference security) _ _ (_p2mH145 (_root_.CurrentAFT.ActualControls.bodyReference security) source) color
  have h := _p2mH131 security _ 1 (by norm_num) hprofile output
  simpa only [_root_.CurrentAFT.RootReferenceColumns.ordinaryDensityAt, _root_.CurrentAFT.RationalMassLiftProgram.actual, LinearMap.comp_apply, mul_one] using h
open _root_.P2M60f02c0e renaming h141 → _p2mH141
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h142 (security order : ℕ) (horder : 1 ≤ order) (source : _root_.CurrentAFT.ActualControls.SafePalette security) (root : _root_.CurrentAFT.CycleRootExpansion.Root security)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.ActualControls.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |(_root_.CurrentAFT.RationalOrdinaryFamilyProgram.firstActual security order horder source root arity).val colors centers| ≤ _root_.CurrentAFT.RationalTensorInverseProgram.actualBound security := by
  rw [← congrFun (congrFun (congrFun (_p2mH146 security order horder source root) arity) colors) centers]
  exact _p2mH185 _ _ _ (_p2mH192 security)
    (_p2mH141 security source root) arity colors centers
open _root_.P2M60f02c0e renaming h142 → _p2mH142
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h140 (security order : ℕ) (horder : 1 ≤ order) (source : _root_.CurrentAFT.ActualControls.SafePalette security)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.ActualControls.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |(_root_.CurrentAFT.RaisingChannels.bodyLeading security order horder (Pi.single source 1) arity).val colors centers| ≤ 1 := by
  rw [← congrFun (congrFun (congrFun (_p2mH144 security order horder source) arity) colors) centers]
  unfold _root_.CurrentAFT.RationalBackgroundTable.firstTable
  split_ifs
  · norm_num
  · exact _p2mH145 (_root_.CurrentAFT.ActualControls.bodyReference security) source _
  · norm_num
open _root_.P2M60f02c0e renaming h140 → _p2mH140
end
open _root_.P2M60f02c0e renaming h140 → _p2mH140
open _root_.P2M60f02c0e renaming h141 → _p2mH141
open _root_.P2M60f02c0e renaming h142 → _p2mH142
open _root_.P2M60f02c0e renaming h144 → _p2mH144
open _root_.P2M60f02c0e renaming h145 → _p2mH145
open _root_.P2M60f02c0e renaming h146 → _p2mH146
open _root_.P2M60f02c0e renaming h148 → _p2mH148
end CurrentAFT.RationalOrdinaryFamilyProgram
open _root_.P2M60f02c0e renaming h140 → _p2mH140
open _root_.P2M60f02c0e renaming h141 → _p2mH141
open _root_.P2M60f02c0e renaming h142 → _p2mH142
open _root_.P2M60f02c0e renaming h144 → _p2mH144
open _root_.P2M60f02c0e renaming h145 → _p2mH145
open _root_.P2M60f02c0e renaming h146 → _p2mH146
open _root_.P2M60f02c0e renaming h148 → _p2mH148
end
open _root_.P2M60f02c0e renaming h140 → _p2mH140
open _root_.P2M60f02c0e renaming h141 → _p2mH141
open _root_.P2M60f02c0e renaming h142 → _p2mH142
open _root_.P2M60f02c0e renaming h144 → _p2mH144
open _root_.P2M60f02c0e renaming h145 → _p2mH145
open _root_.P2M60f02c0e renaming h146 → _p2mH146
open _root_.P2M60f02c0e renaming h148 → _p2mH148
namespace CurrentAFT.LocalRaisingBounds
end CurrentAFT.LocalRaisingBounds
namespace CurrentAFT.LocalRaisingBounds.positiveInverse
end CurrentAFT.LocalRaisingBounds.positiveInverse
namespace CurrentAFT.OrdinaryRaising
end CurrentAFT.OrdinaryRaising
namespace CurrentAFT.OrdinaryRaising.deviation
end CurrentAFT.OrdinaryRaising.deviation
namespace CurrentAFT.RootLocalDenominators
end CurrentAFT.RootLocalDenominators
namespace CurrentAFT.RootLocalDenominators.ordinaryPolynomial
end CurrentAFT.RootLocalDenominators.ordinaryPolynomial
namespace CurrentAFT.RootMeanPrimary.meanProfile
end CurrentAFT.RootMeanPrimary.meanProfile
namespace CurrentAFT.RootUnselectedBlockChannel.channel.match_1
end CurrentAFT.RootUnselectedBlockChannel.channel.match_1
namespace CurrentAFT.RootUnselectedBlockChannel.positivePolynomial
end CurrentAFT.RootUnselectedBlockChannel.positivePolynomial
section
namespace CurrentAFT.RootOrdinaryDataIdentity
open AFT
open scoped Classical
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h221 (security : ℕ) :
    _root_.CurrentAFT.RootMeanPrimary.meanProfile security .free 0 = _root_.CurrentAFT.OrdinaryRaising.deviation security := by
  unfold _root_.CurrentAFT.RootMeanPrimary.meanProfile _root_.CurrentAFT.OrdinaryRaising.deviation
  rw [_p2mH211, _root_.CurrentAFT.RootLocalDenominators.uniformReference_eq]
open _root_.P2M60f02c0e renaming h221 → _p2mH221
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h222 (security order : ℕ) (horder : 1 ≤ order) :
    _root_.CurrentAFT.RootMeanPrimary.positiveAtom security order horder .free 0 = _root_.CurrentAFT.OrdinaryRaising.positiveAtom security order horder := by
  unfold _root_.CurrentAFT.RootMeanPrimary.positiveAtom _root_.CurrentAFT.OrdinaryRaising.positiveAtom
  congr 1
  exact congrArg _root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile (_p2mH221 security)
open _root_.P2M60f02c0e renaming h222 → _p2mH222
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h223 (security order : ℕ) (horder : 1 ≤ order) :
    _root_.CurrentAFT.RootMeanPrimary.positiveFamily security order horder .free 0 = _root_.CurrentAFT.OrdinaryRaising.positiveFamily security order horder := by
  unfold _root_.CurrentAFT.RootMeanPrimary.positiveFamily _root_.CurrentAFT.OrdinaryRaising.positiveFamily
  rw [_p2mH222]
open _root_.P2M60f02c0e renaming h223 → _p2mH223
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h224 (security order : ℕ) (horder : 1 ≤ order) :
    _root_.CurrentAFT.RootMeanPrimary.positiveInverse security order horder .free 0 = _root_.CurrentAFT.OrdinaryRaising.positiveInverse security order horder := by
  unfold _root_.CurrentAFT.RootMeanPrimary.positiveInverse _root_.CurrentAFT.OrdinaryRaising.positiveInverse
  rw [_p2mH223]
open _root_.P2M60f02c0e renaming h224 → _p2mH224
end
open _root_.P2M60f02c0e renaming h221 → _p2mH221
open _root_.P2M60f02c0e renaming h222 → _p2mH222
open _root_.P2M60f02c0e renaming h223 → _p2mH223
open _root_.P2M60f02c0e renaming h224 → _p2mH224
end CurrentAFT.RootOrdinaryDataIdentity
open _root_.P2M60f02c0e renaming h221 → _p2mH221
open _root_.P2M60f02c0e renaming h222 → _p2mH222
open _root_.P2M60f02c0e renaming h223 → _p2mH223
open _root_.P2M60f02c0e renaming h224 → _p2mH224
end
open _root_.P2M60f02c0e renaming h221 → _p2mH221
open _root_.P2M60f02c0e renaming h222 → _p2mH222
open _root_.P2M60f02c0e renaming h223 → _p2mH223
open _root_.P2M60f02c0e renaming h224 → _p2mH224
namespace CurrentAFT.RationalActualFamilyApproximation.interpret
end CurrentAFT.RationalActualFamilyApproximation.interpret
namespace CurrentAFT.RationalFamilyProductProgram.pullback
end CurrentAFT.RationalFamilyProductProgram.pullback
namespace CurrentAFT.RationalOrdinaryFamilyProgram
end CurrentAFT.RationalOrdinaryFamilyProgram
namespace CurrentAFT.RationalOrdinaryFamilyProgram.bodyFirst
end CurrentAFT.RationalOrdinaryFamilyProgram.bodyFirst
namespace CurrentAFT.RationalOrdinaryFamilyProgram.first
end CurrentAFT.RationalOrdinaryFamilyProgram.first
namespace CurrentAFT.RationalOrdinaryFamilyProgram.firstActual
end CurrentAFT.RationalOrdinaryFamilyProgram.firstActual
namespace CurrentAFT.RootOrdinaryDataIdentity
end CurrentAFT.RootOrdinaryDataIdentity
section
namespace CurrentAFT.RationalOrdinaryFamilyProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion CoefficientHilbert
  ControlCoordinates GradedControlAlgebra RationalFamilyProductProgram RationalActualFamilyApproximation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RationalOrdinaryFamilyProgram.ordinaryNormalizedFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalOrdinaryFamilyProgram.ordinaryNormalizedSafeDecidableEq
attribute [local irreducible] Parameters.base primaryLaw centerLaw rootReference PublicParameterProgram.modulus
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h147 (security order : ℕ) : 0 ≤ _root_.CurrentAFT.RationalSingletonProgram.inverseBound security order ∧
    0 ≤ _root_.CurrentAFT.RationalSingletonProgram.inverseErrorConstant security order := by
  have hfirst := _p2mH184 security
  have hpos : 0 ≤ _root_.CurrentAFT.RationalSingletonProgram.positiveBound security := by unfold _root_.CurrentAFT.RationalSingletonProgram.positiveBound; positivity
  have hE := (_p2mH179 security).2
  have hg0 := _p2mH94 order (1 + _root_.CurrentAFT.RationalSingletonProgram.positiveBound security) 0 (by positivity) (by norm_num)
  have hg := _p2mH94 order (1 + _root_.CurrentAFT.RationalSingletonProgram.positiveBound security)
    (_root_.CurrentAFT.RationalRootProfileProgram.meanErrorConstant security) (by positivity) hE
  constructor
  · unfold _root_.CurrentAFT.RationalSingletonProgram.inverseBound; positivity
  · unfold _root_.CurrentAFT.RationalSingletonProgram.inverseErrorConstant; positivity
open _root_.P2M60f02c0e renaming h147 → _p2mH147
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h143 (security order : ℕ) (horder : 1 ≤ order)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.ActualControls.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |(_root_.CurrentAFT.OrdinaryRaising.positiveInverse security order horder arity).val colors centers| ≤
      _root_.CurrentAFT.RationalSingletonProgram.inverseBound security order := by
  have h := _p2mH182 security order horder .free 0 arity colors centers
  rw [_p2mH224] at h
  exact h
open _root_.P2M60f02c0e renaming h143 → _p2mH143
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h139 (security order : ℕ) (horder : 1 ≤ order) (source : _root_.CurrentAFT.ActualControls.SafePalette security) (root : _root_.CurrentAFT.CycleRootExpansion.Root security)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.ActualControls.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |(_root_.CurrentAFT.RootReferenceColumns.ordinaryAt security order horder root (Pi.single source 1) arity).val colors centers| ≤
      _root_.CurrentAFT.RationalOrdinaryFamilyProgram.atRootBound security order := by
  have h := _p2mH101 order (_root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.RationalOrdinaryFamilyProgram.firstActual security order horder source root))
    (_root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.OrdinaryRaising.positiveInverse security order horder))
    (_root_.CurrentAFT.RationalTensorInverseProgram.actualBound security) (_root_.CurrentAFT.RationalSingletonProgram.inverseBound security order)
    (_p2mH192 security) (_p2mH147 security order).1
    (_p2mH142 security order horder source root) (_p2mH143 security order horder) arity colors centers
  rw [_p2mH84] at h
  exact h
open _root_.P2M60f02c0e renaming h139 → _p2mH139
end
open _root_.P2M60f02c0e renaming h139 → _p2mH139
open _root_.P2M60f02c0e renaming h143 → _p2mH143
open _root_.P2M60f02c0e renaming h147 → _p2mH147
end CurrentAFT.RationalOrdinaryFamilyProgram
open _root_.P2M60f02c0e renaming h139 → _p2mH139
open _root_.P2M60f02c0e renaming h143 → _p2mH143
open _root_.P2M60f02c0e renaming h147 → _p2mH147
end
open _root_.P2M60f02c0e renaming h139 → _p2mH139
open _root_.P2M60f02c0e renaming h143 → _p2mH143
open _root_.P2M60f02c0e renaming h147 → _p2mH147
namespace CurrentAFT.RationalOrdinaryFamilyProgram.current
end CurrentAFT.RationalOrdinaryFamilyProgram.current
namespace CurrentAFT.RootReferenceColumns.hybridAt
end CurrentAFT.RootReferenceColumns.hybridAt
namespace CurrentAFT.SelectedOrdinaryHybrid
end CurrentAFT.SelectedOrdinaryHybrid
namespace CurrentAFT.SelectedOrdinaryHybrid.independentChannel
end CurrentAFT.SelectedOrdinaryHybrid.independentChannel
section
namespace CurrentAFT.RationalRootGroupProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion
  ControlCoordinates GradedControlAlgebra RationalFamilyProductProgram RationalActualFamilyApproximation
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalRootGroupProgram.groupProgramFinDecidableEq
attribute [local irreducible] Parameters.base primaryLaw centerLaw rootReference PublicParameterProgram.modulus
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h163 (security order : ℕ) : 0 ≤ _root_.CurrentAFT.RationalRootGroupProgram.errorConstant security order := by unfold _root_.CurrentAFT.RationalRootGroupProgram.errorConstant; positivity
open _root_.P2M60f02c0e renaming h163 → _p2mH163
end
open _root_.P2M60f02c0e renaming h163 → _p2mH163
end CurrentAFT.RationalRootGroupProgram
open _root_.P2M60f02c0e renaming h163 → _p2mH163
end
open _root_.P2M60f02c0e renaming h163 → _p2mH163
namespace CurrentAFT.CurrentGroupSourcePadding.groupKind.match_1
end CurrentAFT.CurrentGroupSourcePadding.groupKind.match_1
namespace CurrentAFT.GroupSourcePadding.indexEquiv
end CurrentAFT.GroupSourcePadding.indexEquiv
namespace CurrentAFT.GroupSourcePadding.sourceDecode
end CurrentAFT.GroupSourcePadding.sourceDecode
namespace CurrentAFT.RationalPackedRootProgram
end CurrentAFT.RationalPackedRootProgram
namespace CurrentAFT.RationalPackedRootProgram.actualMetadata
end CurrentAFT.RationalPackedRootProgram.actualMetadata
namespace CurrentAFT.RationalPackedRootProgram.nativeKind
end CurrentAFT.RationalPackedRootProgram.nativeKind
namespace CurrentAFT.RationalPackedRootProgram.nativeKind.match_1
end CurrentAFT.RationalPackedRootProgram.nativeKind.match_1
namespace CurrentAFT.RationalPackedRootProgram.nativeRole
end CurrentAFT.RationalPackedRootProgram.nativeRole
namespace CurrentAFT.RationalPackedRootProgram.nativeRole.match_3
end CurrentAFT.RationalPackedRootProgram.nativeRole.match_3
namespace CurrentAFT.RationalPackedRootProgram.sourceIndex
end CurrentAFT.RationalPackedRootProgram.sourceIndex
section
namespace CurrentAFT.RationalPackedRootProgram
open AFT ActualBlockFock TaggedSelection PairedRootPlacement CurrentGroupSourcePadding CurrentRootOrdering
  CurrentRootSlotIndex CurrentRectangleIndex GroupSourcePadding RationalRootGroupProgram CycleRootExpansion
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedSignedFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedSignedVertexDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount rootReference rootLaw
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h159 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (source : _root_.CurrentAFT.PairedRootInput.GroupInput selection tagged) :
    |_root_.CurrentAFT.RootWeightedSynthesis.weightedCoefficient selection tagged layout source| ≤ 1 := by
  apply _p2mH21
  intro roots
  rw [Finset.abs_prod]
  apply Finset.prod_le_one (fun _ _ => abs_nonneg _)
  intro index _
  have hlo := (_root_.CurrentAFT.CycleRootExpansion.rootReference security).nonneg (_root_.CurrentAFT.RootWeightedSynthesis.taggedOutput selection tagged source index)
  have hhi := (_root_.CurrentAFT.CycleRootExpansion.rootReference security).atom_le_one (_root_.CurrentAFT.RootWeightedSynthesis.taggedOutput selection tagged source index)
  split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
open _root_.P2M60f02c0e renaming h159 → _p2mH159
end
open _root_.P2M60f02c0e renaming h159 → _p2mH159
end CurrentAFT.RationalPackedRootProgram
open _root_.P2M60f02c0e renaming h159 → _p2mH159
end
open _root_.P2M60f02c0e renaming h159 → _p2mH159
namespace CurrentAFT.CurrentRootSlotIndex
end CurrentAFT.CurrentRootSlotIndex
namespace CurrentAFT.CurrentRootSlotIndex.taggedSlots
end CurrentAFT.CurrentRootSlotIndex.taggedSlots
section
namespace CurrentAFT.RationalPackedRootProgram
open AFT TaggedSelection PairedRootPlacement CurrentGroupSourcePadding CurrentRootOrdering
  CurrentRootSlotIndex CycleRootExpansion
open ActualBlockFock (BlockIndex)
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedUntaggedFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedUntaggedSigmaDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedUntaggedSumDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedUntaggedProdDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount rootReference
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h156 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (root : _root_.CurrentAFT.CurrentRootSlotIndex.Slot selection tagged) :
    root ∈ Finset.univ.map (_root_.CurrentAFT.PairedRootInput.sourceEmbedding selection tagged) ↔
      _root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged root ∈ tagged := by
  constructor
  · intro h
    obtain ⟨index, _, he⟩ := Finset.mem_map.mp h
    rw [← he]
    change _root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged
      (_root_.CurrentAFT.PairedRootPlacement.tagEmbedding selection tagged (tagged.equivFin.symm index)) ∈ tagged
    rw [_root_.CurrentAFT.PairedRootPlacement.tag_image]
    exact (tagged.equivFin.symm index).property
  · intro h
    let tag : tagged := ⟨_root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged root, h⟩
    refine Finset.mem_map.mpr ⟨tagged.equivFin tag, Finset.mem_univ _, ?_⟩
    change _root_.CurrentAFT.PairedRootPlacement.tagEmbedding selection tagged (tagged.equivFin.symm (tagged.equivFin tag)) = root
    rw [Equiv.symm_apply_apply]
    exact (_root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged).injective (_root_.CurrentAFT.PairedRootPlacement.tag_image selection tagged tag)
open _root_.P2M60f02c0e renaming h156 → _p2mH156
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h158 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (source : _root_.CurrentAFT.PairedRootInput.GroupInput selection tagged) :
    _root_.CurrentAFT.RootWeightedSynthesis.untaggedWeight selection tagged source =
      ∏ root : _root_.CurrentAFT.CurrentRootSlotIndex.Slot selection tagged, if _root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged root ∈ tagged then 1 else
        (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight ((source root.fst).1 root.snd) := by
  unfold _root_.CurrentAFT.RootWeightedSynthesis.untaggedWeight
  have hc : (Finset.univ.map (_root_.CurrentAFT.PairedRootInput.sourceEmbedding selection tagged))ᶜ =
      Finset.univ.filter (fun root => _root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged root ∉ tagged) := by
    ext root
    simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, _p2mH156]
  rw [hc, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro root _
  by_cases ht : _root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged root ∈ tagged <;> simp only [ht, not_true_eq_false,
    not_false_eq_true, ite_true, ite_false]
open _root_.P2M60f02c0e renaming h158 → _p2mH158
end
open _root_.P2M60f02c0e renaming h156 → _p2mH156
open _root_.P2M60f02c0e renaming h158 → _p2mH158
end CurrentAFT.RationalPackedRootProgram
open _root_.P2M60f02c0e renaming h156 → _p2mH156
open _root_.P2M60f02c0e renaming h158 → _p2mH158
end
open _root_.P2M60f02c0e renaming h156 → _p2mH156
open _root_.P2M60f02c0e renaming h158 → _p2mH158
namespace CurrentAFT.RationalPackedRootProgram.nativeRole.match_1
end CurrentAFT.RationalPackedRootProgram.nativeRole.match_1
section
namespace CurrentAFT.RationalPackedRootProgram
open AFT TaggedSelection PairedRootPlacement CurrentRootSlotIndex CycleRootExpansion
open ActualBlockFock (BlockIndex)
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedUntaggedBoundsFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedUntaggedBoundsSumDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedUntaggedBoundsSigmaDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount rootReference
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h157 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (source : _root_.CurrentAFT.PairedRootInput.GroupInput selection tagged) :
    0 ≤ _root_.CurrentAFT.RootWeightedSynthesis.untaggedWeight selection tagged source ∧
      _root_.CurrentAFT.RootWeightedSynthesis.untaggedWeight selection tagged source ≤ 1 := by
  rw [_p2mH158]
  have hb (root : _root_.CurrentAFT.CurrentRootSlotIndex.Slot selection tagged) :
      0 ≤ (if _root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged root ∈ tagged then (1 : ℝ) else
        (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight ((source root.fst).1 root.snd)) ∧
      (if _root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged root ∈ tagged then (1 : ℝ) else
        (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight ((source root.fst).1 root.snd)) ≤ 1 := by
    split_ifs
    · norm_num
    · exact ⟨_root_.AFT.FiniteDist.nonneg _ _, _root_.AFT.FiniteDist.atom_le_one _ _⟩
  exact ⟨Finset.prod_nonneg (fun root _ => (hb root).1),
    Finset.prod_le_one (fun root _ => (hb root).1) (fun root _ => (hb root).2)⟩
open _root_.P2M60f02c0e renaming h157 → _p2mH157
end
open _root_.P2M60f02c0e renaming h157 → _p2mH157
end CurrentAFT.RationalPackedRootProgram
open _root_.P2M60f02c0e renaming h157 → _p2mH157
end
open _root_.P2M60f02c0e renaming h157 → _p2mH157
section
namespace CurrentAFT.RationalPackedRootProgram
open AFT TaggedSelection PairedRootPlacement CurrentGroupSourcePadding CurrentRootOrdering
  CurrentRectangleIndex RationalRootGroupProgram CycleRootExpansion ActualControls
open ActualBlockFock (BlockIndex)
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedControlFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedControlSafeDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h150 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (sourcePrimary : Fin r → _root_.CurrentAFT.ActualControls.Palette security) (sourceBody : Fin s → _root_.CurrentAFT.ActualControls.SafePalette security)
    (source : _root_.CurrentAFT.PairedRootInput.GroupInput selection tagged) :
    |_root_.CurrentAFT.PairedRootInput.controlKernel selection tagged (_root_.CurrentAFT.WeightedPointKernelProgram.actualKernel security sourcePrimary sourceBody)
      (fun group => (source group).2)| ≤ 1 := by
  exact _p2mH256 security sourcePrimary sourceBody _ _
open _root_.P2M60f02c0e renaming h150 → _p2mH150
end
open _root_.P2M60f02c0e renaming h150 → _p2mH150
end CurrentAFT.RationalPackedRootProgram
open _root_.P2M60f02c0e renaming h150 → _p2mH150
end
open _root_.P2M60f02c0e renaming h150 → _p2mH150
namespace CurrentAFT.RationalRootGroupProgram
end CurrentAFT.RationalRootGroupProgram
namespace CurrentAFT.RationalRootGroupProgram.LocalRole
end CurrentAFT.RationalRootGroupProgram.LocalRole
namespace CurrentAFT.RationalRootGroupProgram.LocalRole.center
end CurrentAFT.RationalRootGroupProgram.LocalRole.center
namespace CurrentAFT.RationalRootGroupProgram.LocalRole.leg
end CurrentAFT.RationalRootGroupProgram.LocalRole.leg
namespace CurrentAFT.RationalRootGroupProgram.LocalRole.ordinary
end CurrentAFT.RationalRootGroupProgram.LocalRole.ordinary
namespace CurrentAFT.RationalRootGroupProgram.LocalRole.primary
end CurrentAFT.RationalRootGroupProgram.LocalRole.primary
namespace CurrentAFT.RationalRootGroupProgram.LocalRole.queue
end CurrentAFT.RationalRootGroupProgram.LocalRole.queue
namespace CurrentAFT.RationalRootGroupProgram.localTable
end CurrentAFT.RationalRootGroupProgram.localTable
namespace CurrentAFT.RationalRootGroupProgram.localTable.match_1
end CurrentAFT.RationalRootGroupProgram.localTable.match_1
namespace CurrentAFT.RationalRootGroupProgram.role
end CurrentAFT.RationalRootGroupProgram.role
namespace CurrentAFT.RationalRootGroupProgram.role.match_3
end CurrentAFT.RationalRootGroupProgram.role.match_3
namespace CurrentAFT.RationalRootGroupProgram.sourceNatural
end CurrentAFT.RationalRootGroupProgram.sourceNatural
namespace CurrentAFT.RationalRootGroupProgram.sourceNatural.match_1
end CurrentAFT.RationalRootGroupProgram.sourceNatural.match_1
namespace CurrentAFT.RationalRootGroupProgram.table
end CurrentAFT.RationalRootGroupProgram.table
namespace CurrentAFT.RootReferenceColumns.legAt
end CurrentAFT.RootReferenceColumns.legAt
namespace CurrentAFT.RootReferenceColumns.reducedColumn.match_1
end CurrentAFT.RootReferenceColumns.reducedColumn.match_1
namespace CurrentAFT.RootReferenceColumns.singletonAt
end CurrentAFT.RootReferenceColumns.singletonAt
namespace CurrentAFT.RootReferenceColumns.unselectedAt.match_1
end CurrentAFT.RootReferenceColumns.unselectedAt.match_1
section
namespace CurrentAFT.RationalRootGroupProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion CoefficientHilbert
  ControlCoordinates GradedControlAlgebra RationalFamilyProductProgram RationalActualFamilyApproximation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RationalRootGroupProgram.groupBoundsFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalRootGroupProgram.groupBoundsSafeDecidableEq
attribute [local irreducible] Parameters.base primaryLaw centerLaw rootReference
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h169 (security order : ℕ) (roots : _root_.CurrentAFT.RootTaggedSelected.RootPair security) (source : _root_.CurrentAFT.ActualControls.Palette security)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.ActualControls.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |(_root_.CurrentAFT.RootReferenceColumns.primaryAt security order roots source arity).val colors centers| ≤ _root_.CurrentAFT.RationalRootGroupProgram.primaryBound security order := by
  let numerator := _root_.CurrentAFT.LocalRaisingLinear.completeFamilyLinear security order
    (_root_.CurrentAFT.RootMassColumns.primaryMassAt security roots (_root_.CurrentAFT.CoefficientHilbert.centerLinear (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (Pi.single source 1)))
  have h := _p2mH101 order (_root_.CurrentAFT.RationalActualFamilyApproximation.data security order numerator) (_root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.LocalRaisingBounds.positiveInverse security order))
    (_root_.CurrentAFT.LocalCoefficientPointBounds.numeratorBound security) (_root_.CurrentAFT.RationalNormalizedPrimaryProgram.inverseBound security order)
    (_p2mH63 security) (_p2mH137 security order)
    (_p2mH64 security order roots source) (_p2mH136 security order)
    arity colors centers
  rw [_p2mH84] at h
  exact h
open _root_.P2M60f02c0e renaming h169 → _p2mH169
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h164 (security order : ℕ) (horder : 1 ≤ order) (source : _root_.CurrentAFT.ActualControls.SafePalette security)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.ActualControls.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |(_root_.CurrentAFT.SelectedOrdinaryHybrid.independentChannel security order horder (Pi.single source 1) arity).val colors centers| ≤
      (Fintype.card (_root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) : ℝ)^2 * _root_.CurrentAFT.RationalSingletonProgram.inverseBound security order := by
  have h := _p2mH101 order
    (_root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.RaisingChannels.bodyLeading security order horder (Pi.single source 1)))
    (_root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.OrdinaryRaising.positiveInverse security order horder))
    1 (_root_.CurrentAFT.RationalSingletonProgram.inverseBound security order) (by norm_num)
    (_p2mH147 security order).1
    (_p2mH140 security order horder source)
    (_p2mH143 security order horder) arity colors centers
  rw [_p2mH84] at h
  have hchannel : _root_.CurrentAFT.SelectedOrdinaryHybrid.independentChannel security order horder (Pi.single source 1) =
      _root_.CurrentAFT.GradedControlAlgebra.familyProduct (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order
        (_root_.CurrentAFT.RaisingChannels.bodyLeading security order horder (Pi.single source 1))
        (_root_.CurrentAFT.OrdinaryRaising.positiveInverse security order horder) := by rfl
  rw [hchannel]
  simpa only [_root_.CurrentAFT.RationalActualFamilyApproximation.data, one_mul] using h
open _root_.P2M60f02c0e renaming h164 → _p2mH164
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h167 (security order : ℕ) (horder : 1 ≤ order) (source : _root_.CurrentAFT.ActualControls.SafePalette security) (root : _root_.CurrentAFT.CycleRootExpansion.Root security)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.ActualControls.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |(_root_.CurrentAFT.RootReferenceColumns.hybridAt security order horder root (Pi.single source 1) arity).val colors centers| ≤ _root_.CurrentAFT.RationalRootGroupProgram.ordinaryBound security order := by
  have hmean : |∑ other : _root_.CurrentAFT.CycleRootExpansion.Root security, (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight other *
      (_root_.CurrentAFT.RootReferenceColumns.ordinaryAt security order horder other (Pi.single source 1) arity).val colors centers| ≤
      _root_.CurrentAFT.RationalOrdinaryFamilyProgram.atRootBound security order := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ other : _root_.CurrentAFT.CycleRootExpansion.Root security, (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight other * _root_.CurrentAFT.RationalOrdinaryFamilyProgram.atRootBound security order := by
        apply Finset.sum_le_sum
        intro other _
        rw [abs_mul, abs_of_nonneg ((_root_.CurrentAFT.CycleRootExpansion.rootReference security).nonneg other)]
        exact mul_le_mul_of_nonneg_left
          (_p2mH139 security order horder source other arity colors centers)
          ((_root_.CurrentAFT.CycleRootExpansion.rootReference security).nonneg other)
      _ = _ := by rw [← Finset.sum_mul, _root_.AFT.FiniteDist.sum_one, one_mul]
  simp only [_root_.CurrentAFT.RootReferenceColumns.hybridAt, Pi.sub_apply, Pi.add_apply, Submodule.coe_sub, Submodule.coe_add,
    Finset.sum_apply, Submodule.coe_sum, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  exact (abs_sub _ _).trans ((add_le_add
    ((abs_add_le _ _).trans (add_le_add (_p2mH164 security order horder source arity colors centers)
      (_p2mH139 security order horder source root arity colors centers))) hmean).trans_eq
      (by unfold _root_.CurrentAFT.RationalRootGroupProgram.ordinaryBound; ring))
open _root_.P2M60f02c0e renaming h167 → _p2mH167
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h165 (security order : ℕ) (horder : 1 ≤ order) (root : _root_.CurrentAFT.CycleRootExpansion.Root security)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.ActualControls.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |(_root_.CurrentAFT.RootReferenceColumns.legAt security order horder root arity).val colors centers| ≤ _root_.CurrentAFT.RationalRootGroupProgram.legBound security order := by
  have h := _p2mH101 order (_root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.RationalUnselectedLegProgram.numeratorActual security order horder root))
    (_root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.RootLegReciprocal.reciprocal security order))
    (_root_.CurrentAFT.RationalUnselectedLegProgram.numeratorBound security) (_root_.CurrentAFT.RationalUnselectedLegProgram.inverseBound security order)
    (_p2mH204 security).1 (_p2mH202 security order).1
    (_p2mH198 security order horder root)
    (_p2mH197 security order) arity colors centers
  rw [_p2mH84] at h
  exact h
open _root_.P2M60f02c0e renaming h165 → _p2mH165
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h170 (security order : ℕ) (horder : 1 ≤ order) (bodyRole : _root_.CurrentAFT.UniformBodyProfiles.BodyRole)
    (queue : ℤ) (root : _root_.CurrentAFT.CycleRootExpansion.Root security) (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order)
    (colors : Fin arity.val.1.val → _root_.CurrentAFT.ActualControls.Palette security) (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |(_root_.CurrentAFT.RootReferenceColumns.singletonAt security order horder bodyRole queue root arity).val colors centers| ≤ _root_.CurrentAFT.RationalRootGroupProgram.singletonBound security order := by
  have h := _p2mH101 order (_root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.RootReferenceColumns.singletonFirstAt security order horder bodyRole queue root))
    (_root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.RootMeanPrimary.positiveInverse security order horder bodyRole queue))
    (_root_.CurrentAFT.RationalSingletonProgram.firstBound security) (_root_.CurrentAFT.RationalSingletonProgram.inverseBound security order)
    (_p2mH184 security) (_p2mH147 security order).1
    (_p2mH181 security order horder bodyRole queue root)
    (_p2mH182 security order horder bodyRole queue) arity colors centers
  rw [_p2mH84] at h
  exact h
open _root_.P2M60f02c0e renaming h170 → _p2mH170
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h168 (security order : ℕ) : 1 ≤ _root_.CurrentAFT.RationalRootGroupProgram.pointBound security order := by
  unfold _root_.CurrentAFT.RationalRootGroupProgram.pointBound
  linarith [abs_nonneg (_root_.CurrentAFT.RationalRootGroupProgram.primaryBound security order), abs_nonneg (_root_.CurrentAFT.RationalRootGroupProgram.ordinaryBound security order),
    abs_nonneg (_root_.CurrentAFT.RationalRootGroupProgram.legBound security order), abs_nonneg (_root_.CurrentAFT.RationalRootGroupProgram.singletonBound security order)]
open _root_.P2M60f02c0e renaming h168 → _p2mH168
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h166 {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s) (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security))
    (group : _root_.CurrentAFT.PairedRootPlacement.ActiveGroup selection tagged) (source : _root_.CurrentAFT.ActualRootGroupedChannel.Input selection tagged group)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.ActualControls.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |(_root_.CurrentAFT.RootReferenceColumns.reducedColumn order horder queue selection tagged group source arity).val colors centers| ≤ _root_.CurrentAFT.RationalRootGroupProgram.pointBound security order := by
  have hp : _root_.CurrentAFT.RationalRootGroupProgram.primaryBound security order ≤ _root_.CurrentAFT.RationalRootGroupProgram.pointBound security order := by
    unfold _root_.CurrentAFT.RationalRootGroupProgram.pointBound
    linarith [le_abs_self (_root_.CurrentAFT.RationalRootGroupProgram.primaryBound security order), abs_nonneg (_root_.CurrentAFT.RationalRootGroupProgram.ordinaryBound security order),
      abs_nonneg (_root_.CurrentAFT.RationalRootGroupProgram.legBound security order), abs_nonneg (_root_.CurrentAFT.RationalRootGroupProgram.singletonBound security order)]
  have ho : _root_.CurrentAFT.RationalRootGroupProgram.ordinaryBound security order ≤ _root_.CurrentAFT.RationalRootGroupProgram.pointBound security order := by
    unfold _root_.CurrentAFT.RationalRootGroupProgram.pointBound
    linarith [le_abs_self (_root_.CurrentAFT.RationalRootGroupProgram.ordinaryBound security order), abs_nonneg (_root_.CurrentAFT.RationalRootGroupProgram.primaryBound security order),
      abs_nonneg (_root_.CurrentAFT.RationalRootGroupProgram.legBound security order), abs_nonneg (_root_.CurrentAFT.RationalRootGroupProgram.singletonBound security order)]
  have hl : _root_.CurrentAFT.RationalRootGroupProgram.legBound security order ≤ _root_.CurrentAFT.RationalRootGroupProgram.pointBound security order := by
    unfold _root_.CurrentAFT.RationalRootGroupProgram.pointBound
    linarith [le_abs_self (_root_.CurrentAFT.RationalRootGroupProgram.legBound security order), abs_nonneg (_root_.CurrentAFT.RationalRootGroupProgram.ordinaryBound security order),
      abs_nonneg (_root_.CurrentAFT.RationalRootGroupProgram.primaryBound security order), abs_nonneg (_root_.CurrentAFT.RationalRootGroupProgram.singletonBound security order)]
  have hs : _root_.CurrentAFT.RationalRootGroupProgram.singletonBound security order ≤ _root_.CurrentAFT.RationalRootGroupProgram.pointBound security order := by
    unfold _root_.CurrentAFT.RationalRootGroupProgram.pointBound
    linarith [le_abs_self (_root_.CurrentAFT.RationalRootGroupProgram.singletonBound security order), abs_nonneg (_root_.CurrentAFT.RationalRootGroupProgram.ordinaryBound security order),
      abs_nonneg (_root_.CurrentAFT.RationalRootGroupProgram.legBound security order), abs_nonneg (_root_.CurrentAFT.RationalRootGroupProgram.primaryBound security order)]
  rcases group with (primary | ordinary) | kept
  · exact (_p2mH169 security order _ source.2 arity colors centers).trans hp
  · exact (_p2mH167 security order horder source.2 (source.1 (0 : Fin 1)) arity colors centers).trans ho
  · rcases hk : kept.val.val with leg | (center | point)
    · simpa only [_root_.CurrentAFT.RootReferenceColumns.reducedColumn, _root_.CurrentAFT.RootReferenceColumns.unselectedAt, hk] using
        (_p2mH165 security order horder (source.1 (0 : Fin 1)) arity colors centers).trans hl
    · have hfree : _root_.CurrentAFT.RootReferenceColumns.singletonAt security order horder .free queue (source.1 (0 : Fin 1)) =
          _root_.CurrentAFT.RootReferenceColumns.singletonAt security order horder .free 0 (source.1 (0 : Fin 1)) := by rfl
      simpa only [_root_.CurrentAFT.RootReferenceColumns.reducedColumn, _root_.CurrentAFT.RootReferenceColumns.unselectedAt, hk, hfree] using
        (_p2mH170 security order horder .free queue (source.1 (0 : Fin 1)) arity colors centers).trans hs
    · simpa only [_root_.CurrentAFT.RootReferenceColumns.reducedColumn, _root_.CurrentAFT.RootReferenceColumns.unselectedAt, hk] using
        (_p2mH170 security order horder .queue queue (source.1 (0 : Fin 1)) arity colors centers).trans hs
open _root_.P2M60f02c0e renaming h166 → _p2mH166
end
open _root_.P2M60f02c0e renaming h164 → _p2mH164
open _root_.P2M60f02c0e renaming h165 → _p2mH165
open _root_.P2M60f02c0e renaming h166 → _p2mH166
open _root_.P2M60f02c0e renaming h167 → _p2mH167
open _root_.P2M60f02c0e renaming h168 → _p2mH168
open _root_.P2M60f02c0e renaming h169 → _p2mH169
open _root_.P2M60f02c0e renaming h170 → _p2mH170
end CurrentAFT.RationalRootGroupProgram
open _root_.P2M60f02c0e renaming h164 → _p2mH164
open _root_.P2M60f02c0e renaming h165 → _p2mH165
open _root_.P2M60f02c0e renaming h166 → _p2mH166
open _root_.P2M60f02c0e renaming h167 → _p2mH167
open _root_.P2M60f02c0e renaming h168 → _p2mH168
open _root_.P2M60f02c0e renaming h169 → _p2mH169
open _root_.P2M60f02c0e renaming h170 → _p2mH170
end
open _root_.P2M60f02c0e renaming h164 → _p2mH164
open _root_.P2M60f02c0e renaming h165 → _p2mH165
open _root_.P2M60f02c0e renaming h166 → _p2mH166
open _root_.P2M60f02c0e renaming h167 → _p2mH167
open _root_.P2M60f02c0e renaming h168 → _p2mH168
open _root_.P2M60f02c0e renaming h169 → _p2mH169
open _root_.P2M60f02c0e renaming h170 → _p2mH170
namespace CurrentAFT.OrdinaryRaising.positiveInverse
end CurrentAFT.OrdinaryRaising.positiveInverse
section
namespace CurrentAFT.RationalPackedRootProgram
open AFT TaggedSelection PairedRootPlacement CurrentGroupSourcePadding CurrentRootOrdering
  CurrentRectangleIndex RationalRootGroupProgram CycleRootExpansion ActualControls
  ControlCoordinates GradedControlAlgebra RationalFamilyProductProgram RationalActualFamilyApproximation
open ActualBlockFock (BlockIndex)
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedProductFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h152 {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s) (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security))
    (source : _root_.CurrentAFT.PairedRootInput.GroupInput selection tagged) :
    _root_.CurrentAFT.RationalFamilyWordProduct.current order (_root_.CurrentAFT.RationalPackedRootProgram.groupCount selection tagged) (fun index => _root_.CurrentAFT.RationalActualFamilyApproximation.data security order
      (_root_.CurrentAFT.RootReferenceColumns.reducedColumn order horder queue selection tagged
        (_root_.CurrentAFT.RationalPackedRootProgram.ordering selection tagged index) (source (_root_.CurrentAFT.RationalPackedRootProgram.ordering selection tagged index)))) =
      _root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.RationalPackedRootProgram.productActual order horder queue selection tagged source) := by
  unfold _root_.CurrentAFT.RationalActualFamilyApproximation.data
  rw [_p2mH106]
  have hp := (_root_.CurrentAFT.RationalPackedRootProgram.ordering selection tagged).prod_comp (fun group =>
    _root_.CurrentAFT.RootReferenceColumns.reducedColumn order horder queue selection tagged group (source group))
  exact congrArg (fun family : _root_.CurrentAFT.BackgroundFamilies.ActualFamily security order =>
    fun arity => (family arity).val) hp
open _root_.P2M60f02c0e renaming h152 → _p2mH152
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h151 (security order : ℕ) : 1 ≤ _root_.CurrentAFT.RationalPackedRootProgram.localGrowth security order :=
  _p2mH94 _ _ _ ((by norm_num : (0 : ℝ) ≤ 1).trans (_p2mH168 security order))
    (_p2mH163 security order)
open _root_.P2M60f02c0e renaming h151 → _p2mH151
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h153 {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s) (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security))
    (source : _root_.CurrentAFT.PairedRootInput.GroupInput selection tagged)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.ActualControls.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |_root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.RationalPackedRootProgram.productActual order horder queue selection tagged source) arity colors centers| ≤
      (_root_.CurrentAFT.RationalPackedRootProgram.localGrowth security order)^(_root_.CurrentAFT.RationalPackedRootProgram.groupCount selection tagged) := by
  let A := _root_.CurrentAFT.RationalRootGroupProgram.pointBound security order
  have hA : 0 ≤ A := (by norm_num : (0 : ℝ) ≤ 1).trans (_p2mH168 security order)
  have hscale : (Nat.card (_root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) : ℝ)^2 * A ≤ _root_.CurrentAFT.RationalPackedRootProgram.localGrowth security order := by
    apply le_trans _ (_p2mH95 order A (_root_.CurrentAFT.RationalRootGroupProgram.errorConstant security order))
    gcongr
    have hE := _p2mH163 security order
    linarith
  have h := _p2mH107 order (_root_.CurrentAFT.RationalPackedRootProgram.groupCount selection tagged)
    (fun index => _root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.RootReferenceColumns.reducedColumn order horder queue selection tagged
      (_root_.CurrentAFT.RationalPackedRootProgram.ordering selection tagged index) (source (_root_.CurrentAFT.RationalPackedRootProgram.ordering selection tagged index)))) A (_root_.CurrentAFT.RationalPackedRootProgram.localGrowth security order)
    hA (_p2mH151 security order) hscale
    (fun index => _p2mH166 order horder queue selection tagged _ _) arity colors centers
  rw [_p2mH152] at h
  exact h
open _root_.P2M60f02c0e renaming h153 → _p2mH153
end
open _root_.P2M60f02c0e renaming h151 → _p2mH151
open _root_.P2M60f02c0e renaming h152 → _p2mH152
open _root_.P2M60f02c0e renaming h153 → _p2mH153
end CurrentAFT.RationalPackedRootProgram
open _root_.P2M60f02c0e renaming h151 → _p2mH151
open _root_.P2M60f02c0e renaming h152 → _p2mH152
open _root_.P2M60f02c0e renaming h153 → _p2mH153
end
open _root_.P2M60f02c0e renaming h151 → _p2mH151
open _root_.P2M60f02c0e renaming h152 → _p2mH152
open _root_.P2M60f02c0e renaming h153 → _p2mH153
namespace CurrentAFT.RationalPackedRootProgram.errorConstant
end CurrentAFT.RationalPackedRootProgram.errorConstant
namespace CurrentAFT.RationalPackedRootProgram.kernelErrorBound
end CurrentAFT.RationalPackedRootProgram.kernelErrorBound
namespace CurrentAFT.RationalPackedRootProgram.localGrowth
end CurrentAFT.RationalPackedRootProgram.localGrowth
namespace CurrentAFT.RationalPackedRootProgram.uniformScalarBound
end CurrentAFT.RationalPackedRootProgram.uniformScalarBound
namespace CurrentAFT.RationalPackedRootProgram.uniformScalarError
end CurrentAFT.RationalPackedRootProgram.uniformScalarError
section
namespace CurrentAFT.RationalPackedRootProgram
open AFT TaggedSelection PairedRootPlacement CycleRootExpansion ActualControls
  GradedControlAlgebra RationalActualFamilyApproximation
open ActualBlockFock (BlockIndex)
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedBoundFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedBoundSafeDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedBoundSumDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedBoundSigmaDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount rootReference
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h154 (security order : ℕ) : 0 ≤ _root_.CurrentAFT.RationalPackedRootProgram.responseBound security order := by
  unfold _root_.CurrentAFT.RationalPackedRootProgram.responseBound
  have hc := (by norm_num : (0:ℝ)≤1).trans (_p2mH151 security order)
  positivity
open _root_.P2M60f02c0e renaming h154 → _p2mH154
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h149 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (sourcePrimary : Fin r → _root_.CurrentAFT.ActualControls.Palette security) (sourceBody : Fin s → _root_.CurrentAFT.ActualControls.SafePalette security)
    (source : _root_.CurrentAFT.PairedRootInput.GroupInput selection tagged) :
    |_root_.CurrentAFT.RationalPackedRootProgram.actualScalar selection tagged layout sourcePrimary sourceBody source|≤1 := by
  have hc := _p2mH150 selection tagged sourcePrimary sourceBody source
  have hu := _p2mH157 selection tagged source
  have hw := _p2mH159 selection tagged layout source
  unfold _root_.CurrentAFT.RationalPackedRootProgram.actualScalar
  rw [abs_mul, abs_mul, abs_of_nonneg hu.1]
  exact (mul_le_mul (mul_le_mul hc hu.2 hu.1 (by norm_num)) hw (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
open _root_.P2M60f02c0e renaming h149 → _p2mH149
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h155 {security r s : ℕ} (order : ℕ) (horder : 1≤order) (queue : ℤ)
    (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s) (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security))
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security) (hdegree : r+s≤order) (htags : tagged.card≤order)
    (sourcePrimary : Fin r → _root_.CurrentAFT.ActualControls.Palette security) (sourceBody : Fin s → _root_.CurrentAFT.ActualControls.SafePalette security)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.ActualControls.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |_root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.ActualRootResponse.response order horder queue selection tagged layout
      (_root_.CurrentAFT.WeightedPointKernelProgram.actualKernel security sourcePrimary sourceBody)) arity colors centers| ≤
      _root_.CurrentAFT.RationalPackedRootProgram.responseBound security order := by
  have hc := _p2mH151 security order
  have hcn := (by norm_num : (0:ℝ)≤1).trans hc
  have hcount : _root_.CurrentAFT.RationalPackedRootProgram.groupCount selection tagged≤2*order := by
    have hk := _p2mH28 selection tagged
    unfold _root_.CurrentAFT.RationalPackedRootProgram.groupCount
    omega
  rw [_p2mH26 order horder queue selection tagged (_root_.CurrentAFT.CurrentRootOrdering.keptOrdering selection tagged)]
  simp only [_root_.CurrentAFT.RationalActualFamilyApproximation.data, Finset.sum_apply, Submodule.coe_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ _index : Fin ((_root_.CurrentAFT.CurrentRectangleIndex.colors security)^((_root_.CurrentAFT.RationalPackedRootProgram.groupCount selection tagged)*3)),
        (_root_.CurrentAFT.RationalPackedRootProgram.localGrowth security order)^(_root_.CurrentAFT.RationalPackedRootProgram.groupCount selection tagged) := by
      apply Finset.sum_le_sum
      intro index _
      cases _root_.CurrentAFT.CurrentGroupSourcePadding.decode selection tagged (_root_.CurrentAFT.CurrentRootOrdering.keptOrdering selection tagged) index with
      | none => simpa only [Option.elim_none, Pi.zero_apply, Submodule.coe_zero, abs_zero] using pow_nonneg hcn (_root_.CurrentAFT.RationalPackedRootProgram.groupCount selection tagged)
      | some source =>
        simp only [Option.elim_some, Pi.smul_apply, Submodule.coe_smul, smul_eq_mul]
        have hp : (∏ group, _root_.CurrentAFT.RootReferenceColumns.reducedColumn order horder queue selection tagged group (source group)) =
            _root_.CurrentAFT.RationalPackedRootProgram.productActual order horder queue selection tagged source := by
          unfold _root_.CurrentAFT.RationalPackedRootProgram.productActual
          apply Finset.prod_congr (by ext; simp)
          intro group _
          rfl
        rw [hp, abs_mul]
        exact (mul_le_mul (_p2mH149 selection tagged layout sourcePrimary sourceBody source)
          (_p2mH153 order horder queue selection tagged source arity colors centers)
          (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
    _ = (_root_.CurrentAFT.CurrentRectangleIndex.colors security:ℝ)^((_root_.CurrentAFT.RationalPackedRootProgram.groupCount selection tagged)*3)*
        (_root_.CurrentAFT.RationalPackedRootProgram.localGrowth security order)^(_root_.CurrentAFT.RationalPackedRootProgram.groupCount selection tagged) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
    _ ≤ _root_.CurrentAFT.RationalPackedRootProgram.responseBound security order := by
      unfold _root_.CurrentAFT.RationalPackedRootProgram.responseBound
      have hq : (1:ℝ)≤_root_.CurrentAFT.CurrentRectangleIndex.colors security := by exact_mod_cast _root_.CurrentAFT.CurrentRectangleIndex.colors_pos security
      exact mul_le_mul (pow_le_pow_right₀ hq (by omega)) (pow_le_pow_right₀ hc hcount)
        (pow_nonneg hcn _) (by positivity)
open _root_.P2M60f02c0e renaming h155 → _p2mH155
end
open _root_.P2M60f02c0e renaming h149 → _p2mH149
open _root_.P2M60f02c0e renaming h154 → _p2mH154
open _root_.P2M60f02c0e renaming h155 → _p2mH155
end CurrentAFT.RationalPackedRootProgram
open _root_.P2M60f02c0e renaming h149 → _p2mH149
open _root_.P2M60f02c0e renaming h154 → _p2mH154
open _root_.P2M60f02c0e renaming h155 → _p2mH155
end
open _root_.P2M60f02c0e renaming h149 → _p2mH149
open _root_.P2M60f02c0e renaming h154 → _p2mH154
open _root_.P2M60f02c0e renaming h155 → _p2mH155
namespace CurrentAFT.FullResponseWeightedIdentity
end CurrentAFT.FullResponseWeightedIdentity
namespace CurrentAFT.FullResponseWeightedIdentity.choiceAverage
end CurrentAFT.FullResponseWeightedIdentity.choiceAverage
namespace CurrentAFT.FullResponseWeightedIdentity.selected
end CurrentAFT.FullResponseWeightedIdentity.selected
namespace CurrentAFT.FullResponseWeightedIdentity.sourceKernel
end CurrentAFT.FullResponseWeightedIdentity.sourceKernel
namespace CurrentAFT.RationalFullResponseProgram
end CurrentAFT.RationalFullResponseProgram
namespace CurrentAFT.RationalFullResponseProgram.tags
end CurrentAFT.RationalFullResponseProgram.tags
namespace CurrentAFT.RationalPackedRootProgram.responseBound
end CurrentAFT.RationalPackedRootProgram.responseBound
namespace CurrentAFT.WeightedPointKernelProgram.actualKernel
end CurrentAFT.WeightedPointKernelProgram.actualKernel
section
namespace CurrentAFT.RationalFullResponseProgram
open AFT ActualBlockFock TaggedSelection GradedControlAlgebra LocalCoefficientFamily
  ActualControls ProposalPrimary ControlCoordinates ControlProduct CanonicalReconstruction
  UniformTaggedOutput ActualRootFamily FullResponsePointFormula RationalActualFamilyApproximation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension
  primaryLaw bodyReference
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h116 (security order : ℕ) : 1+((_root_.CurrentAFT.RationalFullResponseProgram.tags security order).card:ℝ) ≤ _root_.CurrentAFT.RationalFullResponseProgram.tagCountBound security order := by
  have hb : 1 ≤ Fintype.card (_root_.CurrentAFT.ActualBlockFock.BlockIndex security) := by
    rw [_p2mH39]
    have h := _p2mH29 security
    omega
  have h := (Finset.card_filter_le (s := _root_.CurrentAFT.FullResponseEnumeration.boundedSubsets (_root_.CurrentAFT.ActualBlockFock.BlockIndex security) order)
    (p := fun tagged => 2 ≤ tagged.card)).trans (_p2mH40 order hb)
  rw [_p2mH39] at h
  unfold _root_.CurrentAFT.RationalFullResponseProgram.tagCountBound _root_.CurrentAFT.RationalFullResponseProgram.tags
  exact_mod_cast Nat.add_le_add_left h 1
open _root_.P2M60f02c0e renaming h116 → _p2mH116
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h117 {security order : ℕ} {tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)} (h : tagged ∈ _root_.CurrentAFT.RationalFullResponseProgram.tags security order) :
    tagged.card ≤ order := (_p2mH41 order tagged).mp (Finset.mem_filter.mp h).1
open _root_.P2M60f02c0e renaming h117 → _p2mH117
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h114 {Index : Type*} (indices : Finset Index) (first : ℝ) (terms : Index → ℝ)
    (bound : ℝ) (hfirst : |first| ≤ bound) (hterms : ∀ index ∈ indices, |terms index| ≤ bound) :
    |first+∑ index ∈ indices, terms index| ≤ (1+(indices.card:ℝ))*bound := by
  have hs := (Finset.abs_sum_le_sum_abs terms indices).trans (Finset.sum_le_sum hterms)
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  exact (abs_add_le _ _).trans ((add_le_add hfirst hs).trans_eq (by ring))
open _root_.P2M60f02c0e renaming h114 → _p2mH114
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h115 (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (source : _root_.CurrentAFT.FullResponsePointFormula.Index security order) (chosen : _root_.CurrentAFT.TaggedSelection.Selection security source.1.val.1.val source.1.val.2.val)
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |_root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.FullResponseWeightedIdentity.selected security order horder queue source chosen layout)
      arity colors centers| ≤ _root_.CurrentAFT.RationalFullResponseProgram.rootBound security order := by
  have ht (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (htags : tagged.card ≤ order) :=
    _p2mH155 order horder queue chosen tagged layout source.1.property htags
      source.2.1 source.2.2 arity colors centers
  have h := _p2mH114 (_root_.CurrentAFT.RationalFullResponseProgram.tags security order) _ _ (_root_.CurrentAFT.RationalPackedRootProgram.responseBound security order)
    (ht ∅ (by simp)) (fun tagged hm => ht tagged (_p2mH117 hm))
  simp only [_root_.CurrentAFT.RationalActualFamilyApproximation.data, _root_.CurrentAFT.FullResponseWeightedIdentity.selected, Pi.add_apply, Submodule.coe_add,
    Finset.sum_apply, Submodule.coe_sum, _root_.CurrentAFT.FullResponseWeightedIdentity.sourceKernel] at *
  exact h.trans (mul_le_mul_of_nonneg_right (_p2mH116 security order)
    (_p2mH154 security order))
open _root_.P2M60f02c0e renaming h115 → _p2mH115
set_option maxRecDepth 8192
theorem _root_.P2M60f02c0e.h113 (security order : ℕ) (horder : 1 ≤ order) (hroom : 2*order ≤ security) (queue : ℤ)
    (source : _root_.CurrentAFT.FullResponsePointFormula.Index security order) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    _root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.FullResponseWeightedIdentity.choiceAverage security order horder hroom queue source layout) arity colors centers =
    (_root_.CurrentAFT.UniformTaggedOutput.choiceLaw security _ _ (_root_.CurrentAFT.ActualRootFamily.primary_room security order hroom source.1) (_root_.CurrentAFT.ActualRootFamily.body_room security order hroom source.1)).expectation
      (fun choice => _root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.FullResponseWeightedIdentity.selected security order horder queue source
        (_root_.CurrentAFT.UniformTaggedOutput.selection security _ _ choice) layout) arity colors centers) := by
  simp only [_root_.CurrentAFT.RationalActualFamilyApproximation.data, _root_.CurrentAFT.FullResponseWeightedIdentity.choiceAverage, _root_.AFT.FiniteDist.expectation, Finset.sum_apply,
    Submodule.coe_sum, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
open _root_.P2M60f02c0e renaming h113 → _p2mH113
set_option maxRecDepth 8192
theorem _root_.CurrentAFT.RationalFullResponseProgram.__p2m_proof_60f02c0e310573087673 (security order : ℕ) (horder : 1 ≤ order) (hroom : 2*order ≤ security) (queue : ℤ)
    (source : _root_.CurrentAFT.FullResponsePointFormula.Index security order) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |_root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.FullResponseWeightedIdentity.choiceAverage security order horder hroom queue source layout)
      arity colors centers| ≤ _root_.CurrentAFT.RationalFullResponseProgram.rootBound security order := by
  rw [_p2mH113]
  exact _p2mH21 _ _ _
    (fun choice => _p2mH115 security order horder queue source _ layout arity colors centers)
end
open _root_.P2M60f02c0e renaming h113 → _p2mH113
open _root_.P2M60f02c0e renaming h114 → _p2mH114
open _root_.P2M60f02c0e renaming h115 → _p2mH115
open _root_.P2M60f02c0e renaming h116 → _p2mH116
open _root_.P2M60f02c0e renaming h117 → _p2mH117
end CurrentAFT.RationalFullResponseProgram
open _root_.P2M60f02c0e renaming h113 → _p2mH113
open _root_.P2M60f02c0e renaming h114 → _p2mH114
open _root_.P2M60f02c0e renaming h115 → _p2mH115
open _root_.P2M60f02c0e renaming h116 → _p2mH116
open _root_.P2M60f02c0e renaming h117 → _p2mH117
end
open _root_.P2M60f02c0e renaming h113 → _p2mH113
open _root_.P2M60f02c0e renaming h114 → _p2mH114
open _root_.P2M60f02c0e renaming h115 → _p2mH115
open _root_.P2M60f02c0e renaming h116 → _p2mH116
open _root_.P2M60f02c0e renaming h117 → _p2mH117
set_option maxRecDepth 65536
theorem solution : (type_of% @_root_.CurrentAFT.RationalFullResponseProgram.__p2m_proof_60f02c0e310573087673) := @_root_.CurrentAFT.RationalFullResponseProgram.__p2m_proof_60f02c0e310573087673
