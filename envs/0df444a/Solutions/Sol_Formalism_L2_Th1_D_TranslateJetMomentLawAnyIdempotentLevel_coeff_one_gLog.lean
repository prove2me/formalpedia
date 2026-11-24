-- Prove2me | solution 1 for Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.coeff_one_gLog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:39:03.122302+00:00
-- url     : https://prove2.me/submissions/45506b33-061b-4d54-b8cb-13a5d91a5139

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FirstMomentIdempotentLaw
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
theorem _root_.solution [CharZero K] {τ : Type} [DecidableEq τ] {l d : ℕ} (hl : l.Prime)
    (φ : ZMod d → τ) (s : ZMod d) (i : τ) :
    coeff (Finsupp.single i 1) (gLog K l φ s) = if i = φ s then 1 else 0 := by
  show (∑ e ∈ Finset.range ((Finsupp.single i 1).degree + 1),
      if Finsupp.single i 1 = Finsupp.single (φ (s - 2 * (e : ZMod d))) ((l ^ 2) ^ e) then
        ((l : K) ^ e)⁻¹ else 0) = _
  have hl1 : l ^ 2 ≠ 1 := by
    have := hl.two_le
    nlinarith
  rw [Finsupp.degree_single, Finset.sum_range_succ, Finset.sum_range_one]
  simp [Finsupp.single_eq_single_iff, hl1, Ne.symm hl1, hl.one_lt.ne']
end Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
