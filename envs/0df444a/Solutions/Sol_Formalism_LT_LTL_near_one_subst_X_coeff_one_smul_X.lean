-- Prove2me | solution 1 for Formalism.LT.LTL.near_one_subst_X_coeff_one_smul_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:08:30.7948+00:00
-- url     : https://prove2.me/submissions/ba59eb6f-94e8-4bfb-b2a7-4b2347530518

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
import Theorems.Thm_Formalism_LT_LTL_Near_mul
import Theorems.Thm_P2M_Formalism_LT_LTL_subst_eq__d02f90c570e8
import Theorems.Thm_Formalism_G_LogCR_Agree_mono
import Theorems.Thm_Formalism_G_LogCR_Agree_mul
import Theorems.Thm_Formalism_LT_InvIntP_Low_add
import Theorems.Thm_Formalism_LT_InvIntP_Low_mono
import Theorems.Thm_Formalism_LT_InvIntP_Low_mul
import Theorems.Thm_Formalism_LT_InvIntP_low_one
import Theorems.Thm_Formalism_LT_InvIntP_low_zero


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
theorem _root_.solution (f : PowerSeries K) (h0 : constantCoeff f = 0) (i : ι) :
    Near 1 (f.subst (MvPowerSeries.X i : MvPowerSeries ι K))
      (((fun _ : ι => coeff 1 f) • (MvPowerSeries.X : ι → MvPowerSeries ι K)) i) := by
  have hX : MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries ι K) = 0 := by simp
  rw [subst_eq' f h0 hX]
  simp only [Pi.smul_apply']
  have hl : Low 1 (coeff 1 f • (MvPowerSeries.X i : MvPowerSeries ι K)) := low_one (by simp)
  refine ⟨?_, hl, ?_⟩
  · refine hl.add ?_
    have := ((low_one hX).mul (low_one hX)).mul (low_zero ((tail2 f).subst (MvPowerSeries.X i : MvPowerSeries ι K)))
    rw [← pow_two] at this
    exact this.mono (by omega)
  · rw [add_sub_cancel_left]
    have := ((low_one hX).mul (low_one hX)).mul (low_zero ((tail2 f).subst (MvPowerSeries.X i : MvPowerSeries ι K)))
    rw [← pow_two] at this
    exact this
end Formalism.LT.LTL
