-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CoboundarySeries.suppOK_Hser
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:52:31.940026+00:00
-- url     : https://prove2.me/submissions/fa131d7e-0c19-4d36-9d1e-76c59230edd4

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffFirstTwoOfThree
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_suppOK_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_suppOK_C_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_suppOK_frob
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_support_ok_g_zero_log
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_support_ok_log_g_zero

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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.CoboundarySeries
open MvPowerSeries
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.CoboundarySeries
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) (σ : K →+* K) {G : MvPowerSeries (Fin 2) K}
    (hG : SuppOK p G) (γ γ' : K) : SuppOK p (Hser p σ G γ γ') := by
  unfold Hser DeS
  exact suppOK_sub (suppOK_sub (suppOK_C_mul _ (suppOK_sub (suppOK_frob hp σ hG) (suppOK_C_mul _ hG)))
    (suppOK_C_mul _ (support_ok_g_zero_log hp))) (suppOK_C_mul _ (support_ok_log_g_zero hp))
end Formalism.InvariantFactorPaths.G7.CoboundarySeries
