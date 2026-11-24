-- Prove2me | solution 1 for Formalism.LT.PadicP.padicInt_norm_le_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:33:43.232791+00:00
-- url     : https://prove2.me/submissions/9e3886dd-c3ff-486a-9de3-def08ed005df

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_IsHomOfSubstEqSmul

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
open Formalism Formalism.LT Formalism.LT.PadicP
open Formalism.G
namespace Formalism.LT.PadicP
theorem _root_.solution {p : ℕ} [Fact p.Prime] (y : ℤ_[p]) (hy : PadicInt.toZMod y = 0) :
    ‖y‖ ≤ ‖(p : ℤ_[p])‖ := by
  have hy' : y ∈ RingHom.ker (PadicInt.toZMod (p := p)) := RingHom.mem_ker.mpr hy
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hy'
  obtain ⟨z, rfl⟩ := hy'
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one z)
end Formalism.LT.PadicP
