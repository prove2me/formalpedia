-- Prove2me | solution 1 for Formalism.L2.Th1.D.SingleLetterLog.at_variable_artin_hasse_eq_one_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:42:44.240479+00:00
-- url     : https://prove2.me/submissions/809e38c2-0e59-4cb7-9dad-028ef0640b8a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_ExponentialSpecification
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionHypothesesOfConditions
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_AtVariableArtinHasseEqOneLog

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
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus oneLog thetaOne)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB UnrOK IsLawOfLog)
open MvPowerSeries (subst HasSubst constantCoeff)
open Formalism.L2.Th1.D.SingleLetterLog
namespace Formalism.L2.Th1.D.SingleLetterLog
theorem _root_.solution {K τ : Type} [Field K] [DecidableEq τ] (l : ℕ) (x : τ) :
    at1 x (lgF K l) = oneLog l x := by
  ext n
  unfold at1
  rw [PowerSeries.coeff_subst_single]
  change _ = oneLog (K := K) l x n
  unfold oneLog lgF
  rw [PowerSeries.coeff_mk]
  split_ifs with h
  · have hd : n.degree = n x := by
      conv_lhs => rw [h]
      simp
    rw [hd]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h3 : (n = Finsupp.single x ((l ^ 2) ^ e)) ↔ n x = (l ^ 2) ^ e :=
      ⟨fun h' => by rw [h']; simp, fun h' => by rw [h, h']⟩
    simp only [h3]
  · symm
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [if_neg]
    intro h'
    apply h
    rw [h']
    simp
end Formalism.L2.Th1.D.SingleLetterLog
