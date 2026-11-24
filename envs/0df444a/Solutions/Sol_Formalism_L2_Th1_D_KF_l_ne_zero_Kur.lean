-- Prove2me | solution 1 for Formalism.L2.Th1.D.KF.l_ne_zero_Kur
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:06:16.249891+00:00
-- url     : https://prove2.me/submissions/9078e89f-ad8a-499f-9e08-b7bf55afd384

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FrobeniusExtensionOnInclusion
import Theorems.Thm_Formalism_L2_Th1_D_KF_norm_l_eq
import Theorems.Thm_Formalism_L2_Th1_D_KF_l_pos_real

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
open Formalism.DworkPowerSeriesWeights (Unram)
open Formalism.InvariantFactorPaths.G7 (UnrOK)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open KF
open Formalism.L2.Th1.D.KF
variable (l : ℕ) [hl : Fact l.Prime]
variable {l}
variable (σ0 : ringA l →+* ringA l) (hiso : ∀ x : ringA l, ‖(σ0 x : ℂ_[l])‖ = ‖(x : ℂ_[l])‖)
namespace Formalism.L2.Th1.D.KF
theorem _root_.solution : (l : MaximalUnramifiedExtension l) ≠ 0 := by
  intro h
  have h2 := congrArg (fun z : MaximalUnramifiedExtension l => (z : ℂ_[l])) h
  push_cast at h2
  have h3 := norm_l_eq l
  rw [h2, norm_zero] at h3
  exact (inv_pos.mpr (l_pos_real l)).ne h3
end Formalism.L2.Th1.D.KF
