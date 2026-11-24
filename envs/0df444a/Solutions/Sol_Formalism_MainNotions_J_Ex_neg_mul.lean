-- Prove2me | solution 1 for Formalism.MainNotions.J.Ex_neg_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:29:44.512018+00:00
-- url     : https://prove2.me/submissions/2c67b27c-0524-43a2-952a-c5c3b5f412ff

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_GandSo
import Theorems.Thm_Formalism_MainNotions_J_Ex_zero
import Theorems.Thm_Formalism_MainNotions_J_Ex_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.J
open MvPowerSeries
variable {ι κ : Type} {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K']
namespace Formalism.MainNotions.J
theorem _root_.solution {f : MvPowerSeries ι K} (hf : constantCoeff f = 0) : Ex (-f) * Ex f = 1 := by
  have hn : constantCoeff (-f) = 0 := by rw [map_neg, hf, neg_zero]
  rw [← Ex_add hn hf]
  simp [Ex_zero]
end Formalism.MainNotions.J
