-- Prove2me | solution 1 for Formalism.LT.LTL.Cong.pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:06:05.453981+00:00
-- url     : https://prove2.me/submissions/ec3473ab-6ebe-4307-af36-f401b29e2171

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
import Theorems.Thm_Formalism_LT_LTL_Near_mul
import Theorems.Thm_Formalism_LT_LTL_Cong_mul
import Theorems.Thm_Formalism_LT_LTL_cong_one
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
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type*}
namespace Formalism.LT.LTL
namespace Cong
theorem _root_.solution {c : K} {A B : MvPowerSeries ι K} (h : Cong c A B) (n : ℕ) :
    Cong c (A ^ n) (B ^ n) := by
  induction n with
  | zero => simpa using cong_one c
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h
end Cong
end Formalism.LT.LTL
