-- Prove2me | solution 1 for Formalism.LT.CoeffP.powCongr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:29:30.433258+00:00
-- url     : https://prove2.me/submissions/460310ef-d860-4d84-963c-5e2f39393efe

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Theorems.Thm_Formalism_LT_CoeffP_Bd_pow
import Theorems.Thm_Formalism_LT_CoeffP_powpj
import Theorems.Thm_Formalism_LT_CoeffP_pow_sub_pow_bd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u v
open Formalism Formalism.LT Formalism.LT.CoeffP
open Formalism.G
namespace Formalism.LT.CoeffP
theorem _root_.solution : Formalism.LT.PowCongr.{u, v} := by
  unfold Formalism.LT.PowCongr
  intro K _ _ ι p hp A B hA hB r hr hD j m
  have hA' : Bd 1 A := hA
  have hB' : Bd 1 B := hB
  have hD' : Bd (‖(p : K)‖ ^ r) (A - B) := by
    intro d
    rw [← norm_pow]
    exact hD d
  have h1 := powpj hp hr hA' hB' hD' j
  have hAj : Bd 1 (A ^ (p ^ j)) := by simpa using Bd.pow hA' zero_le_one (p ^ j)
  have hBj : Bd 1 (B ^ (p ^ j)) := by simpa using Bd.pow hB' zero_le_one (p ^ j)
  have h2 := pow_sub_pow_bd (pow_nonneg (norm_nonneg _) _) hAj hBj h1 m
  intro d
  rw [norm_pow, pow_mul, pow_mul]
  exact h2 d
end Formalism.LT.CoeffP
