-- Prove2me | solution 1 for Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.artin_hasse_log_eq_generic_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:39:02.577378+00:00
-- url     : https://prove2.me/submissions/4358a231-a9d2-4e52-bda5-639daf85a062

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FirstMomentIdempotentLaw
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_single_variable_series
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_eq_expand


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
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog frobVar frobVar_eq_expand)
open MvPowerSeries
open Pair TranslateJetMomentLawAnyIdempotentLevel
open Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
open Pair KernelCokernelKilling
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
theorem _root_.solution {τ : Type} [DecidableEq τ] {d : ℕ} (l : ℕ) (x : τ) (s : ZMod d) :
    at1 x (lgF K l) = gLog K l (fun _ : ZMod d => x) s := by
  ext n
  rw [Formalism.InvariantFactorPaths.G7.coeff_single_variable_series]
  show _ = ∑ e ∈ Finset.range (n.degree + 1),
    if n = Finsupp.single x ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0
  split_ifs with h
  · obtain ⟨m, rfl⟩ : ∃ m, n = Finsupp.single x m := ⟨_, h⟩
    simp only [Finsupp.single_eq_same, Finsupp.degree_single, (Finsupp.single_injective x).eq_iff]
    rw [lgF, PowerSeries.coeff_mk]
  · symm
    refine Finset.sum_eq_zero fun e _ => if_neg ?_
    intro he
    apply h
    rw [he]
    simp
end Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
