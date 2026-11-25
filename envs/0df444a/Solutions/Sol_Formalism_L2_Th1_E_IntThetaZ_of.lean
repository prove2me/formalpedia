-- Prove2me | solution 1 for Formalism.L2.Th1.E.IntThetaZ_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:44:03.213961+00:00
-- url     : https://prove2.me/submissions/b7c92126-7bb4-4353-908f-d95331c34a9a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_ConstantCoeffVecConsPairEqZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ConstantCoeffInVarEqZero
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_map_lgF


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (at1 Simeq cob IsLawOfLog lgF UnrOK)
open Formalism.L2.Th1.C (IntMv IntPS IsPt)
open CompatibleChartOperations
namespace Formalism.L2.Th1.E
theorem _root_.solution (hB0 : Formalism.L2.Th1.D.B0) (hI : IntHyp) (hS : SumEBridge) (hM : MapCob) :
    IntThetaZ := by
  intro K0 K _ _ _ _ _ _ l d N0 N1 _ σ j hU hj hd2 hev F hF ph0 hph0 hF1 hF2 ι _ _ om oms hOw hTr ζ hζ
    R hR hFr O _ _ τ hEnd hBin hCF1 hN hA n _ f f' hff hff' hdual κ _ r V hr hV
  obtain ⟨U0, Φ, hU0, hΦ0, hΦ, hEq⟩ := hI K R hR (lgF K l) (Formalism.L2.Th1.D.expF K l)
    (PowerSeries.map j ph0) hFr O τ hEnd hBin hCF1 hN hA n (ι × Fin N0 × Fin N1) f f' hff hff' hdual
    κ r V hr hV
  have hFj0 : MvPowerSeries.constantCoeff (MvPowerSeries.map j F) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, hF.1, map_zero]
  have hcob : cob (MvPowerSeries.map j F) (lgF K l) = 0 := by
    rw [← Formalism.InvariantFactorPaths.G7.FormalGroupLaws.map_lgF j l, ← hM K0 K j F (lgF K0 l) hF.1, hF.2.2, map_zero]
  have hb : beSum (lgF K l) (Formalism.L2.Th1.D.expF K l) (PowerSeries.map j ph0) =
      (Formalism.L2.Th1.D.sumE (MvPowerSeries.map j (cob F ph0)) :
        MvPowerSeries (Bool × ι × Fin N0 × Fin N1) K) := by
    rw [hM K0 K j F ph0 hF.1]
    exact (hS K (lgF K l) (Formalism.L2.Th1.D.expF K l) hFr.1 (MvPowerSeries.map j F) hFj0 hcob
      (PowerSeries.map j ph0) ι N0 N1).symm
  rw [hb] at hΦ
  obtain ⟨U, hUi, hg⟩ := hB0 K0 K l d N0 N1 σ j hU hj hd2 hev F hF (cob F ph0) hF1 hF2 ι om oms hOw hTr
    ζ hζ U0 Φ hU0 hΦ0 hΦ
  exact ⟨U, hUi, fun g h1 h2 => by rw [hEq]; exact hg g h1 h2⟩
end Formalism.L2.Th1.E
