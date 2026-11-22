-- Prove2me | solution 1 for Formalism.LT.PadicP.coeff_ltLog
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:57:58.466299+00:00
-- url     : https://prove2.me/submissions/9e47e8fe-fe58-4dac-b8c9-74f31b26506a

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
variable {p : ℕ} [hp : Fact p.Prime]
open Classical
namespace Formalism.LT.PadicP
theorem _root_.solution (n : ℕ) :
    coeff n (ltLog p) = if ∃ k : ℕ, p ^ k = n then ((n : ℚ_[p]))⁻¹ else 0 := by
  unfold ltLog
  exact coeff_mk _ _
end Formalism.LT.PadicP
