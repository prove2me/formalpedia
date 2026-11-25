-- Prove2me | solution 1 for Formalism.L2.Th1.D.norm_units_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:10:14.428105+00:00
-- url     : https://prove2.me/submissions/ebb13ef4-cdd3-4a01-b381-9f7031f781f6

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionHypothesesOfLevelOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_CoboundaryCommutesHomomorphism
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_ConstantCoeffVecConsPairEqZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Closure
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SecondLevelOfNormHolds
import Theorems.Thm_Formalism_L2_Th1_D_BrC_logPair
import Theorems.Thm_Formalism_L2_Th1_D_BrC_phNorm_iff
import Theorems.Thm_Formalism_L2_Th1_C_phNormClosed
import Theorems.Thm_Formalism_L2_Th1_C_unit_ball_closed
import Theorems.Thm_Formalism_L2_Th1_D_sigma_isometry


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
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog)
open BrC
namespace Formalism.L2.Th1.D
theorem _root_.solution : NormUnits := by
  intro K _ _ _ l σ hU ph hph S hS α hα
  have hl : 2 ≤ l := by have := hU.2.1; omega
  obtain ⟨hL0, -, hE0, -, -⟩ := BrC.logPair (K := K) hl
  have hσc : Continuous σ := (AddMonoidHomClass.isometry_of_norm σ (sigma_isometry K l σ hU)).continuous
  have hC := Formalism.L2.Th1.C.phNormClosed K (Formalism.G.unitBall K) (Formalism.L2.Th1.C.unit_ball_closed K)
    (lgF K l) (expF K l) ph hL0 hE0 hph
  have hC' : IsClosed {a : K | NormRel l σ ph a} := by
    have h2 := hC.preimage (continuous_id.prodMk hσc)
    convert h2 using 1
    ext a
    exact (BrC.phNorm_iff (l := l) (σ := σ) ph a).symm
  apply closure_minimal (fun a ha => hS a ha) hC'
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨a, ha, h⟩ := hα ε hε
  exact ⟨a, ha, by rw [dist_eq_norm, norm_sub_rev]; exact h⟩
end Formalism.L2.Th1.D
