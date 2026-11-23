-- Prove2me | solution 1 for Formalism.LT.LTL.Near.pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:33.036542+00:00
-- url     : https://prove2.me/submissions/58bc7ba2-d11e-413a-8004-ad5df48b3aac

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
import Theorems.Thm_Formalism_LT_LTL_Near_of_eq
import Theorems.Thm_Formalism_LT_LTL_Near_mul
import Theorems.Thm_Formalism_LT_LTL_near_one
import Theorems.Thm_Formalism_G_LogCR_Agree_mul
import Theorems.Thm_Formalism_LT_InvIntP_Low_mul


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
universe u
open Formalism Formalism.LT Formalism.LT.LTL
open Formalism.G Formalism.G.LogCR Formalism.LT.InvIntP
variable {K : Type u} [NormedField K] {ι : Type*}
namespace Formalism.LT.LTL
namespace Near
theorem _root_.solution {k : ℕ} {A B : MvPowerSeries ι K} (h : Near k A B) (n : ℕ) :
    Near (k * n) (A ^ n) (B ^ n) := by
  induction n with
  | zero => simpa using near_one
  | succ n ih => rw [pow_succ, pow_succ]; exact (ih.mul h).of_eq (by ring)
end Near
end Formalism.LT.LTL
