-- Prove2me | solution 1 for Bl.PlaneOverMembership.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:59.805451+00:00
-- url     : https://prove2.me/submissions/383b6e75-d3ab-4312-b7e8-97052eef7df8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ExponentGrids_ScaledCoordinatesValuationLemma
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_Height
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_SumValuationNat
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_ValAdd
import Definitions.Def_Formalism_TowerValuationBounds_TowerValuationProofs_SumAdditiveCharacterEqZero
import Definitions.Def_Formalism_SizeWindowBrackets_LcvBaseChange
import Definitions.Def_Formalism_QuotientMetricDivisors_PassageScaleFree
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_DualMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FinSup
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RatioMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNStep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PiSumForallInsertOnly
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Example
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_GramBlock
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RescaleCovol
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_TwistFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtImage
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_QuotRealize
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FrameLinearAlgebraFirst
import Definitions.Def_Formalism_HarderNarasimhan_StatementFrame
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_CorankShare_CorankShareProofs_LayerCakeFormula
import Definitions.Def_Formalism_CorankShare_CorankShareProofs_SumNormSqLeHilbertSchmidt
import Definitions.Def_Formalism_HarderNarasimhan_StatementFrameF
import Definitions.Def_Lemmata_PlaneOverMembership_PlOverOfMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Bl.PlaneOverMembership
open NumberField IsDedekindDomain
private theorem plOver_of_mem {K : Type} [Field K] [NumberField K] {g : ℕ} (hg : 0 < g)
    (w : HeightOneSpectrum (𝓞 K)) (h : (g : 𝓞 K) ∈ w.asIdeal) : Formalism.DivisionValues.PlOver g w := by
  classical
  have hc : ((g : 𝓞 K) : K) = (g : K) := by simp
  have hg0 : (g : 𝓞 K) ≠ 0 := by exact_mod_cast hg.ne'
  have hJ : (Ideal.span {(g : 𝓞 K)} : Ideal (𝓞 K)) ≠ 0 := by
    rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  have hm : Associates.mk (Ideal.span {(g : 𝓞 K)}) ≠ 0 := by rwa [ne_eq, Associates.mk_eq_zero]
  have h1 : 1 ≤ (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {(g : 𝓞 K)})).factors := by
    rw [← Associates.prime_pow_dvd_iff_le hm w.associates_irreducible, pow_one,
      Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact h
  unfold Formalism.DivisionValues.PlOver Formalism.DivisionValues.vw
  rw [← hc, ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K _ hJ]
  exact_mod_cast h1
end Bl.PlaneOverMembership
end

set_option autoImplicit false
open Bl Bl.PlaneOverMembership
open NumberField IsDedekindDomain
namespace Bl.PlaneOverMembership
theorem _root_.solution :
  Formalism.AtG.FinitePlaceLiesOverPrime := by
  intro K _ _
  refine ⟨fun w => Ideal.absNorm (Ideal.under ℤ w.asIdeal), fun w => ?_⟩
  have : NeZero w.asIdeal := ⟨w.ne_bot⟩
  have hp : (Ideal.absNorm (Ideal.under ℤ w.asIdeal)).Prime := Nat.absNorm_under_prime w.asIdeal
  exact ⟨hp, plOver_of_mem hp.pos w (Int.absNorm_under_mem w.asIdeal)⟩
end Bl.PlaneOverMembership
