-- Prove2me | solution 1 for Formalism.FG.HeightVAux.toZMod_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:56.171791+00:00
-- url     : https://prove2.me/submissions/cf0bd501-c7b5-484a-80c6-41362e9abe15

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationHomVector
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftFE
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FrobSqV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CongrV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_HeightV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FG Formalism.FG.HeightVAux
open MvPowerSeries Formalism.G Formalism.LT
variable {l : ℕ} [Fact l.Prime]
namespace Formalism.FG.HeightVAux
theorem _root_.solution (x : ℤ_[l]) : PadicInt.toZMod x = 0 ↔ (l : ℤ_[l]) ∣ x := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]
end Formalism.FG.HeightVAux
