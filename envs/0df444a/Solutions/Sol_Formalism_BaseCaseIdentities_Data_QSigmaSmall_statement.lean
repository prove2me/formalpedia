-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.QSigmaSmall_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:54:21.388139+00:00
-- url     : https://prove2.me/submissions/fec3a4c6-7a1d-40b8-ae46-e7287bc4201d

import Definitions.Def_Formalism_FrobeniusBaseCase_CoeffOfFirstMultiplier
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_SecondWayHolds
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseFalseGeneralHolds
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_lR
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_two_K


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.BaseCaseIdentities
noncomputable section
open Classical
open Formalism.BaseCaseIdentities.Data
variable {k : Type*} [Field k] {Z C : Type*} [Fintype Z] [Fintype C] (D : Data k Z C)
namespace Formalism.BaseCaseIdentities.Data
theorem _root_.solution : D.QSigmaSmall := by
  intro hK
  have h2 := D.two_K
  have hi3 : 3 ≤ D.i := by omega
  have hlR := D.lR
  have hpow : (D.l : ℝ) ^ 3 ≤ (D.l : ℝ) ^ D.i := pow_le_pow_right₀ (by linarith) hi3
  unfold qnum sg
  rw [mul_div_assoc', div_lt_one (by positivity)]
  nlinarith [sq_nonneg (D.l : ℝ)]
end Formalism.BaseCaseIdentities.Data
