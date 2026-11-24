-- Prove2me | solution 1 for Formalism.L2.Th1.E.Tor.omegaK_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:23:50.203753+00:00
-- url     : https://prove2.me/submissions/8dd495a7-e5f1-4923-bbf3-c98139ded536

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Series
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Taylor0ConstMul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.F (opU sgStar th0 taylor0)
open Formalism.L2.Th1.B (fExp fLog)
open Formalism.L2.Th1.E.Tor
namespace Formalism.L2.Th1.E.Tor
theorem _root_.solution (d : ℕ) :
    Formalism.L2.Th1.CM.omegaK d ^ 2 = Formalism.L2.Th1.CM.omegaK d - ((d : ℂ) + 1) / 4 := by
  have h : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = d := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    simp
  have hI := Complex.I_sq
  unfold Formalism.L2.Th1.CM.omegaK
  linear_combination (((Real.sqrt d : ℝ) : ℂ) ^ 2 / 4) * hI - (1 / 4) * h
end Formalism.L2.Th1.E.Tor
