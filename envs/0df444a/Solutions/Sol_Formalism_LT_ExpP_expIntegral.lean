-- Prove2me | solution 1 for Formalism.LT.ExpP.expIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:30.560692+00:00
-- url     : https://prove2.me/submissions/ae890bd5-8202-410d-8796-d78508b388ca

import Definitions.Def_Formalism_TorsionNormIteration_Statement
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormNatCastOfNotDvd
import Theorems.Thm_Formalism_LT_ExpP_norm_natCast_eq

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
open Formalism Formalism.LT Formalism.LT.ExpP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.LT.ExpP
theorem _root_.solution : Formalism.LT.ExpIntegral.{u} := by
  intro K _ _ _ p hp hp1 c hc n
  haveI := Fact.mk hp
  rw [norm_div, norm_pow, norm_natCast_eq hp hp1 (Nat.factorial_ne_zero n)]
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpos : 0 < ‖(p : K)‖ ^ padicValNat p n.factorial := pow_pos (norm_pos_iff.2 hp0) _
  rw [div_le_one hpos]
  have hv : (p - 1) * padicValNat p n.factorial ≤ n := by
    have := sub_one_mul_padicValNat_factorial (p := p) n
    omega
  have hc1 : ‖c‖ ≤ 1 := by
    by_contra h
    push_neg at h
    have := one_le_pow₀ (n := p - 1) h.le
    linarith
  calc ‖c‖ ^ n ≤ ‖c‖ ^ ((p - 1) * padicValNat p n.factorial) :=
        pow_le_pow_of_le_one (norm_nonneg _) hc1 hv
    _ = (‖c‖ ^ (p - 1)) ^ padicValNat p n.factorial := pow_mul _ _ _
    _ ≤ ‖(p : K)‖ ^ padicValNat p n.factorial := pow_le_pow_left₀ (by positivity) hc _
end Formalism.LT.ExpP
