-- Prove2me | solution 1 for Formalism.LT.LTL.norm_pi_sub_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:16.092051+00:00
-- url     : https://prove2.me/submissions/fc6dea2e-aab9-470c-b49f-dde330810e14

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma

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
theorem _root_.solution {π : K} (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1) {r : ℕ} (hr : 2 ≤ r) :
    ‖π - π ^ r‖ = ‖π‖ := by
  have hlt : ‖π ^ r‖ < ‖π‖ := by
    rw [norm_pow]; exact pow_lt_self_of_lt_one₀ hπ0 hπ1 (by omega)
  apply le_antisymm
  · have := IsUltrametricDist.norm_add_le_max π (-(π ^ r))
    rw [← sub_eq_add_neg, norm_neg] at this
    exact this.trans (max_le le_rfl hlt.le)
  · have := IsUltrametricDist.norm_add_le_max (π - π ^ r) (π ^ r)
    rw [sub_add_cancel] at this
    rcases le_max_iff.mp this with h | h
    · exact h
    · exact absurd h (not_le.mpr hlt)
end Formalism.LT.LTL
