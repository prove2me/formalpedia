-- Prove2me | solution 1 for Formalism.L2.Th1.D.B4.exp_of_simeq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:27:16.186478+00:00
-- url     : https://prove2.me/submissions/216c0246-5358-4887-a1c1-d62f2c9b41dd

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionHypothesesOfConditions
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_cc_letterLog
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_constantCoeff_mvExp__1e315831da0a
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_subst_mvExp__fa9db9cd36a6


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus BHyp NoLowBidegree letterLog de1 de2 s0 s1 s2 s1' s2' V2 degE)
open Formalism.InvariantFactorPaths.G7 (Simeq DivAB UnrOK IsLawOfLog)
open MvPowerSeries (subst HasSubst constantCoeff)
open B4
open Formalism.L2.Th1.D.B4
namespace Formalism.L2.Th1.D.B4
theorem _root_.solution {K : Type} [NormedField K] [CharZero K] {d : ℕ} [NeZero d] (l : ℕ)
    {D : MvPowerSeries (V2 d) K} (h0 : constantCoeff D = 0)
    (h : Simeq (subst (letterLog (K := K) l) D) 0) :
    Integral (subst (letterLog (K := K) l) (mvExp D)) ∧
      constantCoeff (subst (letterLog (K := K) l) (mvExp D)) = 1 := by
  have hc : ∀ x : V2 d, constantCoeff (letterLog (K := K) l x) = 0 :=
    Formalism.DworkPowerSeriesWeights.Transfer.cc_letterLog l
  have hLL : HasSubst (letterLog (K := K) (d := d) l) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hc
  rw [Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_mvExp' hLL h0]
  unfold Simeq at h
  rw [sub_zero] at h
  exact ⟨h.2, Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.constantCoeff_mvExp' h.1⟩
end Formalism.L2.Th1.D.B4
