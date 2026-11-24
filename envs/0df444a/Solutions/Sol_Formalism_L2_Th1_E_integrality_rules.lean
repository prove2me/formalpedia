-- Prove2me | solution 1 for Formalism.L2.Th1.E.integrality_rules
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:09:41.501402+00:00
-- url     : https://prove2.me/submissions/45092823-ec94-4cab-8984-21ed684158b3

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementU
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Series
import Theorems.Thm_Formalism_L2_Th1_E_Ser_intS_C
import Theorems.Thm_Formalism_L2_Th1_E_Ser_intS_X
import Theorems.Thm_Formalism_L2_Th1_E_Ser_intS_add
import Theorems.Thm_Formalism_L2_Th1_E_Ser_intS_neg
import Theorems.Thm_Formalism_L2_Th1_E_Ser_intS_mul
import Theorems.Thm_Formalism_L2_Th1_E_Ser_intS_pow
import Theorems.Thm_Formalism_L2_Th1_E_Ser_oneUnit_mul
import Theorems.Thm_Formalism_L2_Th1_E_Ser_oneUnit_pow
import Theorems.Thm_Formalism_L2_Th1_E_Ser_oneUnit_of_mul_eq_one
import Theorems.Thm_Formalism_L2_Th1_E_Ser_intS_iff_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Finset
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
namespace Formalism.L2.Th1.E
theorem _root_.solution : IntRules := by
  intro K _ _
  exact ⟨fun _ ha => Ser.intS_C ha, Ser.intS_X, fun _ _ => Ser.intS_add, fun _ => Ser.intS_neg,
    fun _ _ => Ser.intS_mul, fun _ n hf => Ser.intS_pow hf n, fun _ _ => Ser.oneUnit_mul,
    fun _ n hf => Ser.oneUnit_pow hf n, fun _ _ => Ser.oneUnit_of_mul_eq_one,
    Ser.intS_iff_integral⟩
end Formalism.L2.Th1.E
