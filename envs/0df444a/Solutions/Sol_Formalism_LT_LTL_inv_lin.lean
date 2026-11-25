-- Prove2me | solution 1 for Formalism.LT.LTL.inv_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:23:47.494816+00:00
-- url     : https://prove2.me/submissions/9167ee7b-1ff8-4190-8d37-1b23fd9d1a5e

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
import Theorems.Thm_Formalism_LT_LTL_master
import Theorems.Thm_Formalism_LT_LTL_Ldef_zero
import Theorems.Thm_Formalism_LT_LTL_cc_lin
import Theorems.Thm_Formalism_LT_LTL_coeff_lin_single
import Theorems.Thm_Formalism_LT_LTL_integral_lin
import Theorems.Thm_Formalism_LT_InvIntP_low_one


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
variable [Fintype ι] [DecidableEq ι]
variable {p q : ℕ} {π : K} {e e' : PowerSeries K} {a : ι → K}
namespace Formalism.LT.LTL
theorem _root_.solution (_hS : LTSetting K p q π) (he : IsLTSeries q π e) (he' : IsLTSeries q π e')
    (ha : ∀ i, ‖a i‖ ≤ 1) : Inv e e' a 1 (lin a) := by
  refine ⟨cc_lin a, integral_lin a ha, coeff_lin_single a, ?_⟩
  intro d hd
  have hm := master e e' he.2.1 he'.2.1 π he.2.2.1 he'.2.2.1 (cc_lin a)
    (map_zero _) (by rw [sub_zero]; exact low_one (cc_lin a)) d (by omega)
  rw [Ldef_zero e e' he.2.1 he'.2.1, map_zero, pow_one, sub_self, zero_mul, sub_zero] at hm
  exact hm
end Formalism.LT.LTL
